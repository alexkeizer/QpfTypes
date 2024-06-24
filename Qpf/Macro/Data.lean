import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Mathlib.Data.QPF.Multivariate.Constructions.Fix

import Qpf.Macro.Data.Replace
import Qpf.Macro.Data.Count
import Qpf.Macro.Data.View
import Qpf.Macro.Common
import Qpf.Macro.Comp

open Lean Meta Elab.Command
open Elab (Modifiers elabModifiers)
open Parser.Term (namedArgument)
open PrettyPrinter (delab)

private def Array.enum (as : Array α) : Array (Nat × α) :=
  (Array.range as.size).zip as

/--
  Given a natural number `n`, produce a sequence of `n` calls of `.fs`, ending in `.fz`.

  The result corresponds to a `i : PFin2 _` such that `i.toNat == n`
-/
private def PFin2.quoteOfNat : Nat → Term
  | 0   => mkIdent ``PFin2.fz
  | n+1 => Syntax.mkApp (mkIdent ``PFin2.fs) #[(quoteOfNat n)]

private def Fin2.quoteOfNat : Nat → Term
  | 0   => mkIdent ``Fin2.fz
  | n+1 => Syntax.mkApp (mkIdent ``Fin2.fs) #[(quoteOfNat n)]


namespace Data.Command

/-!
  ## Parser
  for `data` and `codata` declarations
-/
section
  open Lean.Parser Lean.Parser.Command

  def inductive_like (cmd : String) : Parser
    := leading_parser cmd >> declId  >> optDeclSig
                        >> Parser.optional  (symbol " :=" <|> " where")
                        >> many ctor
                        >> optDeriving

  def data := inductive_like "data "
  def codata := inductive_like "codata "

  @[command_parser]
  def declaration : Parser
    := leading_parser declModifiers false >> (data <|> codata)
end

/-!
  ## Elaboration
-/
open Elab.Term (TermElabM)

def Name.replacePrefix (old_pref new_pref : Name) : Name → Name
  | Name.anonymous => Name.anonymous
  | Name.str p s   => let p' := if p == old_pref then new_pref
                                else replacePrefix old_pref new_pref p
                      Name.mkStr p' s
  | Name.num p v   => let p' := if p == old_pref then new_pref
                                else replacePrefix old_pref new_pref p
                      Name.mkNum p' v


def Name.stripPrefix (old_pref : Name) : Name → Name
  := Name.replacePrefix old_pref .anonymous



def CtorView.declReplacePrefix (pref new_pref : Name) (ctor: CtorView) : CtorView :=
  let declName := Name.replacePrefix pref new_pref ctor.declName
  {
    declName,
    ref := ctor.ref
    modifiers := ctor.modifiers
    binders := ctor.binders
    type? := ctor.type?
  }


open Parser.Command (declId)
/-- Return a tuple of `declName, declId, shortDeclName` -/
private def addSuffixToDeclId {m} [Monad m] [MonadResolveName m] (declId : Syntax) (suffix : String) :
    m (Name × (TSyntax ``declId) × Name) := do
  let (id, _) := Elab.expandDeclIdCore declId
  let declName := Name.mkStr id suffix
  let declId := mkNode ``declId #[mkIdent declName, mkNullNode]

  let curNamespace ← getCurrNamespace
  let declName := curNamespace ++ declName

  let shortDeclName := Name.mkSimple suffix
  return (declName, declId, shortDeclName)

private def addSuffixToDeclIdent {m} [Monad m] [MonadResolveName m] (declId : Syntax) (suffix : String) :
    m Ident := do
  let (_, uncurriedDeclId, _) ← addSuffixToDeclId declId suffix
  pure ⟨uncurriedDeclId.raw[0]⟩


open Parser in
/--
  Defines the "head" type of a polynomial functor

  That is, it defines a type with exactly as many constructor as the input type, but such that
  all constructors are constants (take no arguments).
-/
def mkHeadT (view : InductiveView) : CommandElabM Name := do
  -- If the original declId was `MyType`, we want to register the head type under `MyType.HeadT`
  let (declName, declId, shortDeclName) ← addSuffixToDeclId view.declId "HeadT"


  let modifiers : Modifiers := {
    isUnsafe := view.modifiers.isUnsafe
  }
  -- The head type is the same as the original type, but with all constructor arguments removed
  let ctors ← view.ctors.mapM fun ctor => do
    let declName := Name.replacePrefix view.declName declName ctor.declName
    pure {
      modifiers, declName,
      ref := ctor.ref
      binders := mkNullNode
      type? := none
      : CtorView
    }

  -- let type ← `(Type $(mkIdent `u))

  -- TODO: make `HeadT` universe polymorphic
  let view := {
    ctors, declId, declName, shortDeclName, modifiers,
    binders         := view.binders.setArgs #[]
    levelNames      := view.levelNames

    ref             := view.ref
    type?           := view.type?

    derivingClasses := view.derivingClasses
    computedFields  := #[]
    : InductiveView
  }

  trace[QPF] "mkHeadT :: elabInductiveViews"
  elabInductiveViews #[view]
  pure declName

open Parser Parser.Term Parser.Command in
/--
  Defines the "child" family of type vectors for an `n`-ary polynomial functor

  That is, it defines a type `ChildT : HeadT → TypeVec n` such that number of inhabitants of
  `ChildT a i` corresponds to the times that constructor `a` takes an argument of the `i`-th type
  argument
-/
def mkChildT (view : InductiveView) (r : Replace) (headTName : Name) : CommandElabM Name := do
  -- If the original declId was `MyType`, we want to register the child type under `MyType.ChildT`
  let (declName, declId, _shortDeclName) ← addSuffixToDeclId view.declId "ChildT"

  let target_type := Syntax.mkApp (mkIdent ``TypeVec) #[quote r.arity]

  let matchAlts ← view.ctors.mapM fun ctor => do
    let head := mkIdent $ Name.replacePrefix view.declName headTName ctor.declName

    let counts := countVarOccurences r ctor.type?
    let counts := counts.map fun n =>
                    Syntax.mkApp (mkIdent ``PFin2) #[quote n]

    `(matchAltExpr| | $head => (!![ $counts,* ]))

  let body ← `(declValEqns|
    $[$matchAlts:matchAlt]*
  )
  let headT := mkIdent headTName

  let cmd ← `(
    def $declId : $headT → $target_type
      $body:declValEqns
  )

  -- trace[QPF] "mkChildT :: elabCommand"
  elabCommand cmd

  pure declName



open Parser.Term in
/--
  Show that the `Shape` type is a qpf, through an isomorphism with the `Shape.P` pfunctor
-/
def mkQpf (shapeView : InductiveView) (ctorArgs : Array CtorArgs) (headT P : Ident) (arity : Nat) : CommandElabM Unit := do
  let (shapeN, _) := Elab.expandDeclIdCore shapeView.declId
  let eqv := mkIdent $ Name.mkStr shapeN "equiv"
  let functor := mkIdent $ Name.mkStr shapeN "functor"
  let q := mkIdent $ Name.mkStr shapeN "qpf"
  let shape := mkIdent shapeN

  let ctors := shapeView.ctors.zip ctorArgs

  /-
    `box` maps objects from the curried form, to the internal uncurried form.
    See below, or [.ofPolynomial] for the signature

    Example, using a simple list type
    ```lean4
     fun x => match x with
    | MyList.Shape.nil a b => ⟨MyList.Shape.HeadT.nil, fun i => match i with
        | 0 => Fin2.elim0 (C:=fun _ => _)
        | 1 => fun j => match j with
                | (.ofNat' 0) => b
        | 2 => fun j => match j with
                | (.ofNat' 0) => a
    ⟩
    | MyList.Shape.cons a as => ⟨MyList.Shape.HeadT.cons, fun i j => match i with
        | 0 => match j with
                | .fz => as
        | 1 => Fin2.elim0 (C:=fun _ => _) j
        | 2 => match j with
                | .fz => a
    ```
  -/

  let boxBody ← ctors.mapM fun (ctor, args) => do
    let argsId  := args.args.map mkIdent
    let alt     := mkIdent ctor.declName
    let headAlt := mkIdent $ Name.replacePrefix shapeView.declName headT.getId ctor.declName

    `(matchAltExpr| | $alt:ident $argsId:ident* => ⟨$headAlt:ident, fun i => match i with
        $(
          ←args.per_type.enum.mapM fun (i, args) => do
            let i := arity - 1 - i
            let body ← if args.size == 0 then
                          -- `(fun j => Fin2.elim0 (C:=fun _ => _) j)
                          `(PFin2.elim0)
                        else
                          let alts ← args.enum.mapM fun (j, arg) =>
                              let arg := mkIdent arg
                              `(matchAltExpr| | $(PFin2.quoteOfNat j) => $arg)
                          `(
                            fun j => match j with
                              $alts:matchAlt*
                          )
            `(matchAltExpr| | $(Fin2.quoteOfNat i) => $body)
        ):matchAlt*
    ⟩)
  let box ← `(
    fun x => match x with
      $boxBody:matchAlt*
  )

  /-
    `unbox` does the opposite of `box`; it maps from uncurried to curried

    fun ⟨head, child⟩ => match head with
    | MyList.Shape.HeadT.nil  => MyList.Shape.nil (child 2 .fz) (child 1 .fz)
    | MyList.Shape.HeadT.cons => MyList.Shape.cons (child 2 .fz) (child 0 .fz)
  -/

  /- the `child` variable in the example above -/
  let unbox_child := mkIdent <|<- Elab.Term.mkFreshBinderName;
  let unboxBody ← ctors.mapM fun (ctor, args) => do
    let alt     := mkIdent ctor.declName
    let headAlt := mkIdent $ Name.replacePrefix shapeView.declName headT.getId ctor.declName

    let args : Array Term ← args.args.mapM fun arg => do
      -- find the pair `(i, j)` such that the argument is the `j`-th occurence of the `i`-th type
      let (i, j) := (args.per_type.enum.map fun (i, t) =>
        -- the order of types is reversed, since `TypeVec`s count right-to-left
        let i := arity - 1 - i
        ((t.indexOf? arg).map fun ⟨j, _⟩ => (i, j)).toList
      ).toList.join.get! 0

      `($unbox_child $(Fin2.quoteOfNat i) $(PFin2.quoteOfNat j))

    let body := Syntax.mkApp alt args

    `(matchAltExpr| | $headAlt:ident => $body)

  let unbox ← `(
    fun ⟨head, $unbox_child⟩ => match head with
        $unboxBody:matchAlt*
  )

  let cmd ← `(
    def $eqv:ident {Γ} : (@TypeFun.ofCurried $(quote arity) $shape) Γ ≃ ($P).Obj Γ where
      toFun     := $box
      invFun    := $unbox
      left_inv  := by
        simp only [Function.LeftInverse]
        intro x
        cases x
        <;> rfl
      right_inv := by
        simp only [Function.RightInverse, Function.LeftInverse]
        intro x
        rcases x with ⟨head, child⟩;
        cases head
        <;> simp
        <;> apply congrArg
        <;> (funext i; fin_cases i)
        <;> (funext (j : PFin2 _); fin_cases j)
        <;> rfl

    instance $functor:ident : MvFunctor (@TypeFun.ofCurried $(quote arity) $shape) where
      map f x   := ($eqv).invFun <| ($P).map f <| ($eqv).toFun <| x

    instance $q:ident : MvQPF.IsPolynomial (@TypeFun.ofCurried $(quote arity) $shape) :=
      .ofEquiv $P $eqv
  )
  trace[QPF] "qpf: {cmd}\n"
  elabCommand cmd

  pure ()









structure MkShapeResult where
  (r : Replace)
  (shape : Name)
  (P : Name)
  (effects : CommandElabM Unit)

open Parser in
def mkShape (view: DataView) : TermElabM MkShapeResult := do
  -- If the original declId was `MyType`, we want to register the shape type under `MyType.Shape`
  let (declName, declId, shortDeclName) ← addSuffixToDeclId view.declId "Shape"


  -- Extract the "shape" functors constructors
  let shapeIdent  := mkIdent shortDeclName
  let ((ctors, ctorArgs), r) ← Replace.shapeOfCtors view shapeIdent
  let ctors := ctors.map (CtorView.declReplacePrefix view.declName declName)

  trace[QPF] "mkShape :: r.getBinders = {←r.getBinders}"
  trace[QPF] "mkShape :: r.expr = {r.expr}"

  -- Assemble it back together, into the shape inductive type
  let binders ← r.getBinders
  let binders := view.binders.setArgs #[binders]
  let modifiers : Modifiers := {
    isUnsafe := view.modifiers.isUnsafe
  }
  let view := {
    ctors, declId, declName, shortDeclName, modifiers, binders,
    levelNames      := []

    ref             := view.ref
    type?           := view.type?

    derivingClasses := view.derivingClasses
    computedFields  := #[]
    : InductiveView
  }

  trace[QPF] "mkShape :: elabInductiveViews :: binders = {view.binders}"

  let PName := Name.mkStr declName "P"
  return ⟨r, declName, PName, do
    elabInductiveViews #[view]

    let headTName ← mkHeadT view
    let childTName ← mkChildT view r headTName

    let PId := mkIdent PName
    -- let u ← Elab.Term.mkFreshBinderName
    let PDeclId := mkNode ``Command.declId #[PId, mkNullNode
      -- #[ TODO: make this universe polymorphic
      --   mkAtom ".{",
      --   mkNullNode #[u],
      --   mkAtom "}"
      -- ]
    ]

    let headTId := mkIdent headTName
    let childTId := mkIdent childTName

    elabCommand <|<- `(
      def $PDeclId:declId :=
        MvPFunctor.mk $headTId $childTId
    )

    mkQpf view ctorArgs headTId PId r.expr.size
  ⟩

open Elab.Term Parser.Term in
/--
  Checks whether the given term is a polynomial functor, i.e., whether there is an instance of
  `IsPolynomial F`, and return that instance (if it exists).
-/
def isPolynomial (view : DataView) (F: Term) : CommandElabM (Option Term) := do
  runTermElabM fun _ => do
    elabBinders view.deadBinders fun _deadVars => do
      let inst_func ← `(MvFunctor $F:term)
      let inst_func ← elabTerm inst_func none

      trace[QPF] "isPolynomial::F = {F}"
      let inst_type ← `(MvQPF.IsPolynomial $F:term)
      trace[QPF] "isPolynomial :: inst_type_stx: {inst_type}"
      let inst_type ← elabTerm inst_type none
      trace[QPF] "isPolynomial :: inst_type: {inst_type}"

      try
        let _ ← synthInstance inst_func
        let inst ← synthInstance inst_type
        return some <|<- delab inst
      catch e =>
        trace[QPF] "{e.toMessageData}"
        return none



/--
  Return a syntax tree for `MvQPF.Fix` or `MvQPF.Cofix` when self is `Data`, resp. `Codata`.
-/
def DataCommand.fixOrCofix : DataCommand → Ident
  | .Data   => mkIdent ``_root_.MvQPF.Fix
  | .Codata => mkIdent ``_root_.MvQPF.Cofix

/--
  Return a syntax tree for `MvPFunctor.W` or `MvPFunctor.M` when self is `Data`, resp. `Codata`.
-/
def DataCommand.fixOrCofixPolynomial : DataCommand → Ident
  | .Data   => mkIdent ``_root_.MvPFunctor.W
  | .Codata => mkIdent ``_root_.MvPFunctor.M

/--
  Take either the fixpoint or cofixpoint of `base` to produce an `Internal` uncurried QPF,
  and define the desired type as the curried version of `Internal`
-/
def mkType (view : DataView) (base : Term × Term × Term) : CommandElabM Unit := do
  trace[QPF] "mkType"
  let uncurriedIdent ← addSuffixToDeclIdent view.declId "Uncurried"
  let baseIdent ← addSuffixToDeclIdent view.declId "Base"
  let baseFunctorIdent ← addSuffixToDeclIdent baseIdent "instMvFunctor"
  let baseQPFIdent ← addSuffixToDeclIdent baseIdent "instQPF"

  let deadBinderNamedArgs ← view.deadBinderNames.mapM fun n =>
        `(namedArgument| ($n:ident := $n:term))
  let uncurriedApplied ← `($uncurriedIdent:ident $deadBinderNamedArgs:namedArgument*)
  let baseApplied ← `($baseIdent:ident $deadBinderNamedArgs:namedArgument*)

  let arity := view.liveBinders.size
  let fix_or_cofix := DataCommand.fixOrCofix view.command

  let ⟨base, functor, q⟩ := base
  trace[QPF] m!"instMvFunctor: {functor}"
  let cmd ← `(
    abbrev $baseIdent:ident $view.deadBinders:bracketedBinder* : TypeFun $(quote <| arity + 1) :=
      $base

    instance $baseFunctorIdent:ident : MvFunctor ($baseApplied) := $functor
    instance $baseQPFIdent:ident : MvQPF ($baseApplied) := $q

    abbrev $uncurriedIdent:ident $view.deadBinders:bracketedBinder* : TypeFun $(quote arity) := $fix_or_cofix $base

    abbrev $(view.declId) $view.deadBinders:bracketedBinder*
      := TypeFun.curried $uncurriedApplied
  )

  trace[QPF] "elabData.cmd = {cmd}"
  elabCommand cmd



open Parser in
/--
  Count the number of arguments to a constructor
-/
partial def countConstructorArgs : Syntax → Nat
  | Syntax.node _ ``Term.arrow #[_, _, tail]  =>  1 + (countConstructorArgs tail)
  | _                                         => 0


open Elab
/--
  Add convenient constructor functions to the environment
-/
def mkConstructors (view : DataView) (shape : Name) : CommandElabM Unit := do
  for ctor in view.ctors do
    trace[QPF] "mkConstructors\n{ctor.declName} : {ctor.type?}"
    let n_args := (ctor.type?.map countConstructorArgs).getD 0

    let args ← (List.range n_args).mapM fun _ =>
      do pure <| mkIdent <|← Elab.Term.mkFreshBinderName
    let args := args.toArray

    let mk := mkIdent ((DataCommand.fixOrCofix view.command).getId ++ `mk)
    let shapeCtor := mkIdent <| Name.replacePrefix view.declName shape ctor.declName
    trace[QPF] "shapeCtor = {shapeCtor}"



    let body := if n_args = 0 then
        `($mk $shapeCtor)
      else
        `(fun $args:ident* => $mk ($shapeCtor $args:ident*))
    let body ← body

    let explicit ← view.getExplicitExpectedType
    let type : Term := TSyntax.mk <|
      (ctor.type?.map fun type =>
        Replace.replaceAllStx view.getExpectedType explicit type
      ).getD explicit
    let modifiers : Modifiers := {
      isNoncomputable := view.modifiers.isNoncomputable
      attrs := #[{
        name := `matchPattern
      }]
    }
    let declId := mkIdent <| Name.stripPrefix (←getCurrNamespace) ctor.declName

    let cmd ← `(
      $(quote modifiers):declModifiers
      def $declId:ident : $type := $body:term
    )

    trace[QPF] "mkConstructor.cmd = {cmd}"
    elabCommand cmd
  return ()




open Macro Comp in
/--
  Top-level elaboration for both `data` and `codata` declarations
-/
@[command_elab declaration]
def elabData : CommandElab := fun stx => do
  let modifiers ← elabModifiers stx[0]
  let decl := stx[1]

  let view ← dataSyntaxToView modifiers decl
  let view ← preProcessCtors view -- Transforms binders into simple lambda types

  let (nonRecView, ⟨r, shape, _P, eff⟩) ← runTermElabM fun _ => do
    let (nonRecView, _rho) ← makeNonRecursive view;
    trace[QPF] "nonRecView: {nonRecView}"
    pure (nonRecView, ←mkShape nonRecView)

  /- Execute the `ComandElabM` side-effects prescribed by `mkShape` -/
  let _ ← eff

  /- Composition pipeline -/
  let base ← elabQpfCompositionBody {
    liveBinders := nonRecView.liveBinders,
    deadBinders := nonRecView.deadBinders,
    type?   := none,
    target  := ←`(
      $(mkIdent shape):ident $r.expr:term*
    )
  }
  trace[QPF] "base = {base}"

  mkType view base
  mkConstructors view shape


end Data.Command
