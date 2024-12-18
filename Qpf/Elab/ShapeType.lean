/-
Copyright (c) 2024 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/

import Lean
import Qpf.Macro.Common
import Qq

/-!
## Shape Types
A shape type is an inductive type where
- all parameters `αᵢ` are of type `Type u`, for the same universe `u`, and
- constructors are only allowed to take arguments of type `αᵢ`,
  for one of the type parameters

Note that this implies that shape types are non-recursive!

-/

open Qq
open Lean Meta Elab Term

/-!
## The core data structure
-/

structure ShapeType.CtorArg (n : Nat) where
  name : Name
  type : Fin n

structure ShapeType.Ctor (n : Nat) where
  name : Name
  args : List (CtorArg n)

structure ShapeType (n : Nat) where
  /-- The name of the shape type -/
  name : Name
  /-- The universe of the parameters, and the resulting type.

  Note that this is used as `Type $univ`, i.e., level zero is `Type` -/
  univ : Level
  /-- The names of the parameters. Note that this list is *only* used for the
  names, the index `n` is authorative for the number of parameters.

  If `params` contains less then `n` names, the other parameters will be given
  anonymous names. Any excess names are simply ignored. -/
  params : List Name
  /-- The constructors -/
  ctors : List (ShapeType.Ctor n)

namespace ShapeType
variable {n : Nat}

/-!
## Defining a shape type as an inductive
-/

/-- The level parameters over which `s` is universe polymorphic.

This is guaranteed to be either an empty list, if `s` is not polymorphic,
or a list with a single element `u`, which will be the universe that all
parameters, and `s` itself, live in. -/
private def levelParamNames (s : ShapeType n) : List Name :=
  match s.univ with
  | .param p => [p]
  | _        => []

private def levelParams (s : ShapeType n) : List Level :=
  s.levelParamNames.map .param

/-- Translate a shape type constructor specification into Lean's internal
representation of an inductive constructor. -/
def Ctor.toInductiveCtor (s : ShapeType n) (params : Array Expr) (c : Ctor n) :
    TermElabM Lean.Constructor := do
  let retTy := mkAppN (.const s.name s.levelParams) params
  let retTy := c.args.foldr (init := retTy) fun arg retTy =>
    Expr.forallE arg.name (params.get! arg.type) retTy .default
  let retTy ← withNewBinderInfos (params.map (·.fvarId!, .implicit)) <|
    mkForallFVars params retTy
  trace[QPF] "{c.name} : {retTy}"
  return {
    name := c.name
    type := retTy
  }

/-- Translate a shape type into Lean's internal representation of an inductive
type. -/
def toInductiveType (s : ShapeType n) : TermElabM Lean.InductiveType := do
  let paramType := Expr.sort (s.univ.succ)
  let paramDecls := Array.ofFn fun (i : Fin n) =>
    (s.params.getD i .anonymous, fun _ => pure paramType)
  withLocalDeclsD paramDecls <| fun params => do
    let type ← mkForallFVars params paramType
    trace[QPF] "{s.name} : {type}"
    withAuxDecl s.name type s.name <| fun _auxDecl => do
      let ctors ← s.ctors.mapM (Ctor.toInductiveCtor s params)
      return {
        name  := s.name
        type  := type
        ctors := ctors
      }

/-- Translate a shape type into Lean's internal representation of a declaration.
-/
def toDeclaration {n} (s : ShapeType n) : TermElabM Lean.Declaration := do
  let levels   := match s.univ with
                  | .param p => [p]
                  | _        => []
  let isUnsafe := false
  return .inductDecl levels n [← s.toInductiveType] isUnsafe

/-- Add `s` to the environment as an inductive type -/
def addToEnvironmentAsInductive (s : ShapeType n) : TermElabM Unit := do
  let decl ← s.toDeclaration
  addAndCompile decl
  mkRecOn s.name
  mkCasesOn s.name
  mkNoConfusion s.name

/-!
## Defining a shape type as a polynomial functor
-/

/-- Convert an array of expressions of type `Type $u` into a single expression
of type `TypeVec.{$u}` -/
def arrayToTypeVecExpr (x : Array Expr) (u : Level) : Expr :=
  let emptyVec :=
    mkApp (.const ``Fin2.elim0 [u.succ.succ])
      (.lam .anonymous q(Fin2 0) q(Type $u) .default)
  Prod.fst <|
    x.foldl (init := (emptyVec, 0)) fun (vec, m) elem =>
      let vec := mkApp3 (.const ``TypeVec.append1 [u]) (toExpr m) vec elem
      (vec, m+1)

/-- Convert a list of expressions of type `Type $u` into a single expression
of type `TypeVec.{$u}` -/
def listToTypeVecExpr (x : List Expr) (u : Level) : Expr :=
  let emptyVec :=
    mkApp (.const ``Fin2.elim0 [u.succ.succ])
      (.lam .anonymous q(Fin2 0) q(Type $u) .default)
  Prod.fst <|
    x.foldl (init := (emptyVec, 0)) fun (vec, m) elem =>
      let vec := mkApp3 (.const ``TypeVec.append1 [u]) (toExpr m) vec elem
      (vec, m+1)

/-- Return an expression of type `PFunctor $n` that is equivalent to the
given shape type -/
def toPFunctor (s : ShapeType n) : Expr :=
  let m := s.ctors.length
  let A : Expr := mkApp (.const ``Fin []) (toExpr m)

  let TV := mkApp (.const ``TypeVec [s.univ]) (toExpr n)
  let u2 := s.univ.succ.succ /- $univ + 2 -/
  let rec mkB : List (Ctor n) → Expr
    | []    => mkApp (.const ``Fin.elim0 [u2]) TV
    | c::cs =>
      have m : Nat := cs.length
      let matchAlt :=
        List.finRange n
          |>.map (fun i =>
              let occurences := c.args.countP (·.type = i)
              mkApp (.const ``Fin []) (toExpr occurences)
            )
          |> (listToTypeVecExpr · s.univ)
      mkApp4 (.const ``Fin.cons [u2])
        (toExpr m)
        (Expr.lam .anonymous q(Fin ($m+1)) TV .default)
        matchAlt
        (mkB cs)
  let B := mkB s.ctors
  mkApp3 (.const ``MvPFunctor.mk [0]) (toExpr n) A B

/-- See `addToEnvironmentAsPFunctor` -/
private def PFunctorSuffix := "_PFunctor"

/-- Add `s` to the environment as a polynomial functor, with the name
`${s.name}._PFunctor`.

Returns the name of the new definition. -/
def addToEnvironmentAsPFunctor (s : ShapeType n) : TermElabM Name := do
  let P := s.toPFunctor
  let name := .str s.name PFunctorSuffix
  let decl := Declaration.defnDecl {
    name        := name
    value       := P
    levelParams := s.levelParamNames
    type        := q(MvPFunctor.{0} $n)
    hints       := .regular 0
    safety      := .safe
  }
  addAndCompile decl
  return name

/-!
## Equivalence proof
-/

section Tactic
open Tactic

def generateBox (s : ShapeType n) : TermElabM Unit := do
  let ty := (Name.anonymous, .implicit, fun _ => pure <| Expr.sort s.univ.succ)
  let tys := Array.range n |>.map fun _ => ty

  withLocalDecls tys <| fun params => do

  let Shape := mkAppN (Expr.const s.name s.levelParams) params
  withLocalDeclD .anonymous Shape <| fun sVar => do

    let paramsVec := sorry /- `params` as a TypeVec -/
    let PObj := mkApp (.const ``MvPFunctor.Obj [0]) (.const (.str s.name PFunctorSuffix) [])

    let casesOn := mkAppN (.const (.str s.name "casesOn") s.levelParams) params
    let motive  := mkLambda .anonymous .default (← mkFreshExprMVar none)
                    (mkApp PObj paramsVec)
    let casesOn := mkApp casesOn motive
/-
open TypeVec (appendFun) in
def Shape.box : Shape α β → Shape._PFunctor.Obj ((Fin2.elim0 ::: α) ::: β) :=
  fun s =>
  @Shape.casesOn α β (fun _ => Shape._PFunctor.Obj ((Fin2.elim0 ::: α) ::: β))
    s
    (fun a b c => Sigma.mk (0 : Fin 2) <|
      appendFun (appendFun Fin2.elim0
        (Fin.cons c Fin.elim0))
        (Fin.cons a <| Fin.cons b Fin.elim0)
    )
    (fun a => Sigma.mk (1 : Fin 2) <|
      appendFun (appendFun Fin2.elim0 (Fin.cons a Fin.elim0)) (Fin.elim0)
    ) -/

/-- Prove the equivalence between the inductive and pfunctor definitions of a
specific shape type.

NOTE: this definition assumes you've already added both definitions to the
environment, through calling `add`
 -/
def proveInductiveEquivPFunctor (s : Name) : TacticM Expr := do
  let originalGoals ← getGoals

  -- stop
  -- let sInfo ← getConstInfoInduct s
  -- sInfo.toConstantVal
  -- let sE := mkConst

  sorry

/-
## Scratch space
-/

inductive Foo (α β : Type u) : Type u
  -- | foo : α → β → α → Foo α β

#check InductiveVal

#eval @id (MetaM _) <| do
  let .inductInfo info ← getConstInfo ``Foo
    | return ()
  println! "type: {info.type}"
  println! "params: {info.numParams}"

set_option trace.QPF true
def shape : ShapeType 2 where
  name := `Shape
  univ := 0
  params := [`α, `β]
  ctors := [
    {
      name := `Shape.foo
      args := [⟨`x, 1⟩, ⟨`y, 1⟩, ⟨.anonymous, 0⟩]
    },
    {
      name := `Shape.bar
      args := [⟨`x, 0⟩]
    }
  ]

#eval shape.addToEnvironmentAsInductive
#eval shape.addToEnvironmentAsPFunctor

#check Shape.foo
#print Shape._PFunctor
#print Shape

#check Shape.rec
