import Lean

import Qpf.Macro.Common
import Qpf.Macro.Data.View

open Lean Meta Elab.Command Elab.Term

/-
  This file contains the core "shape" extraction logic.

  It establishes the `Replace` struct, and corresponding `ReplaceM` state monad, which are used
  to replace all expressions in a type with fresh variables.

-/

structure CtorArgs where
  (args : Array Name)
  (per_type : Array (Array Name))

structure Replace where
  (expr: Array Term)
  (vars: Array Name)
  (ctor: CtorArgs)


private def Replace.new : CommandElabM Replace := 
  do pure ⟨#[], #[], ⟨#[], #[]⟩⟩

private abbrev ReplaceM := StateT Replace CommandElabM

private def CtorArgs.reset : ReplaceM Unit := do
  let r ← StateT.get
  let n := r.vars.size
  let ctor: CtorArgs := ⟨#[], (Array.range n).map fun _ => #[]⟩
  StateT.set ⟨r.expr, r.vars, ctor⟩

private def CtorArgs.get : ReplaceM CtorArgs := do
  pure (←StateT.get).ctor

/--
  The arity of the shape type created *after* replacing, i.e., the size of `r.expr`
-/
def Replace.arity (r : Replace) : Nat :=
  r.expr.size

def Replace.getBinderIdents (r : Replace) : Array Ident :=
  r.vars.map mkIdent

open Parser.Term in
def Replace.getBinders (r : Replace) : CommandElabM <| TSyntax ``bracketedBinder := do
  let names := r.getBinderIdents
  `(bracketedBinderF | ($names* : Type _ ))








private def ReplaceM.identFor (stx : Term) : ReplaceM Ident := do
  let r ← StateT.get
  let ctor := r.ctor
  let argName ← mkFreshBinderName
  let ctor_args := ctor.args.push argName
  -- dbg_trace "\nstx := {stx}\nr.expr := {r.expr}"

  let name ← match r.expr.indexOf? stx with
  | some id => do      
      let ctor_per_type := ctor.per_type.set! id $ (ctor.per_type.get! id).push argName
      let ctor := ⟨ctor_args, ctor_per_type⟩
      StateT.set ⟨r.expr, r.vars, ctor⟩
      pure $ r.vars.get! id
  | none       => do
      let ctor_per_type := ctor.per_type.push #[argName]
      let name ← mkFreshBinderName
      StateT.set ⟨r.expr.push stx, r.vars.push name, ⟨ctor_args, ctor_per_type⟩⟩
      pure name

  return mkIdent name
  



open Lean.Parser in
/--
  Given a sequence of (non-dependent) arrows, replace each unique expression in between the arrows
  with a fresh variable, such that repeated occurrences of the same expression map to the same
  variable
-/
private partial def shapeOf' : Syntax → ReplaceM Syntax
  | Syntax.node _ ``Term.arrow #[arg, arrow, tail] => do
    let ctor_arg ← ReplaceM.identFor ⟨arg⟩ 
    let ctor_tail ← shapeOf' tail

    -- dbg_trace ">> {arg} ==> {ctor_arg}"    
    pure $ mkNode ``Term.arrow #[ctor_arg, arrow, ctor_tail]

  | ctor_type => 
      pure ctor_type



open Lean.Parser in
/--
  Given a sequence of (non-dependent) arrows, change the last expression into `res_type`
-/
private partial def setResultingType (res_type : Syntax) : Syntax → ReplaceM Syntax
  | Syntax.node _ ``Term.arrow #[arg, arrow, tail] => do
    let tail ← setResultingType res_type tail
    pure $ mkNode ``Term.arrow #[arg, arrow, tail]
  | _ => 
      pure res_type


def CtorView.withType? (ctor : CtorView) (type? : Option Syntax) : CtorView := {
  ref       := ctor.ref
  modifiers := ctor.modifiers
  declName  := ctor.declName
  binders   := ctor.binders
  type?     := type?
}

/-
  TODO: currently these functions ignore dead variables, everything is replaced.
  This is OK, we can supply a "dead" value to a live variable, but we lose the ability to have
  dead variables live in a different universe from live ones (since the shape functor will require
  all its arguments to live in the same universe).

  We should instead detect which expressions are dead, and NOT introduce fresh variables for them.
  Instead, have the shape functor also take the same dead binders as the original.
  This does mean that we should check for collisions between the original dead binders, and the 
  fresh variables.
-/




/-- Runs the given action with a fresh instance of `Replace` -/
def Replace.run : ReplaceM α → CommandElabM (α × Replace) := 
  fun x => do 
    let r ← Replace.new
    StateT.run x r

/--
  Extract the constructors for a "shape" functor from the original constructors.
  It replaces all constructor arguments with fresh variables, ensuring that repeated occurences
  of the same type map to a single variable, where "same" refers to a very simple notion of
  syntactic equality. E.g., it does not realize `Nat` and `ℕ` are the same.
-/
def Replace.shapeOfCtors (view : DataView) 
                          (shapeIdent : Syntax) 
    : CommandElabM ((Array CtorView × Array CtorArgs) × Replace) := 
Replace.run <| do
  for var in view.liveBinders do
    let varIdent : Ident := ⟨if var.raw.getKind == ``Parser.Term.binderIdent then
      var.raw[0]
    else
      var.raw
    ⟩
    let varTerm ← `($varIdent:ident)
    let _ ← ReplaceM.identFor varTerm

  let ctors := view.ctors

  let pairs ← ctors.mapM fun ctor => do
    if !ctor.binders.isNone then
      throwErrorAt ctor.binders "Constructor binders are not supported yet, please provide all arguments in the type"

    trace[Qpf.Data] "{ctor.declName}: {ctor.type?}"

    CtorArgs.reset

    let type? ← ctor.type?.mapM $ shapeOf'

    pure $ (CtorView.withType? ctor type?, ←CtorArgs.get)

  let r ← StateT.get
  let ctors := pairs.map Prod.fst;
  let ctorArgs := pairs.map fun ⟨_, ctorArgs⟩ =>
      let per_type := ctorArgs.per_type
      
      let diff := r.vars.size - ctorArgs.per_type.size

      -- HACK: It seems that `Array.append` causes a stack overflow, so we go through `List` for now
      -- TODO: fix this after updating to newer Lean version
      let per_type := per_type.appendList $ (List.range diff).map (fun _ => (#[] : Array Name));
      ⟨ctorArgs.args, per_type⟩

  -- Now that we know how many free variables were introduced, we can fix up the resulting type
  -- of each constructor to be `Shape α_0 α_1 ... α_n`
  let r ← StateT.get
  let res := Syntax.mkApp (TSyntax.mk shapeIdent) r.getBinderIdents

  let ctors ← ctors.mapM fun ctor => do
    let type? ← ctor.type?.mapM (setResultingType res) 
    pure $ CtorView.withType? ctor type?

  pure (ctors, ctorArgs)




/-- Replace syntax in *all* subexpressions -/
partial def Replace.replaceAllStx (find replace : Syntax) : Syntax → Syntax := 
  fun stx =>
    if stx == find then
      replace
    else
      stx.setArgs (stx.getArgs.map (replaceAllStx find replace))



open Parser in
/--
  Given a sequence of arrows e₁ → e₂ → ... → eₙ, check that `eₙ == recType`, and replace all
  *other* occurences (i.e., in e₁ ... eₖ₋₁) of `recType` with `newParam`.

-/
partial def Replace.replaceStx (recType newParam : Term) : Term → CommandElabM Term
  | ⟨stx⟩ => match stx with
    | stx@(Syntax.node _ ``Term.arrow #[arg, arrow, tail]) => do
        pure <| TSyntax.mk <| stx.setArgs #[
          replaceAllStx recType newParam arg,
          arrow,
          ←replaceStx recType newParam ⟨tail⟩ 
        ]

    | stx@(Syntax.node _ ``Term.arrow _) =>
        throwErrorAt stx "Internal bug: encountered an unexpected form of arrow syntax"

    | stx@(Syntax.node _ ``Term.depArrow _) =>
        throwErrorAt stx "Dependent arrows are not supported, please only use plain arrow types"

    | ctor_type => 
        if ctor_type != recType then
          throwErrorAt ctor_type m!"Unexpected constructor resulting type; expected {recType}, found {ctor_type}"
        else
          pure ⟨ctor_type⟩ 



instance : Coe Ident (TSyntax ``Parser.Term.binderIdent) := ⟨
  fun id => mkNode _ #[id]
⟩

open Parser
/--
  Makes a type spefication non-recursive, by replacing all recursive occurences by a fresh bound variable.
  Simultaneously checks that each constructor type, if given, is indeed a sequence of arrows
  ... → ... → ... culminating in the type to be defined.
-/
def makeNonRecursive (view : DataView) : CommandElabM (DataView × Name) := do
  let expected := view.getExpectedType

  let rec ← mkFreshBinderName
  let recId := mkIdent rec

  let view := view.pushLiveBinder recId

  let ctors ← view.ctors.mapM fun ctor => do
    let type? ← ctor.type?.mapM (Replace.replaceStx expected recId <| TSyntax.mk ·)
    return CtorView.withType? ctor type?

  let view := view.setCtors ctors
  pure (view, rec)