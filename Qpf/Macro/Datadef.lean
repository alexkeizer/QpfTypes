import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Mathlib.Data.QPF.Multivariate.Constructions.Fix
import Qpf.Qpf.Multivariate.Constructions.DeepThunk

import Qpf.Macro.Datadef.View
import Qpf.Macro.Data.Replace
import Qpf.Macro.Common
import Qpf.Macro.Comp

open Lean Meta Elab.Command Elab.Term MatchExpr
open Elab (Modifiers elabModifiers)
open Parser.Term (namedArgument)
open PrettyPrinter (delab)


-- Little helper function to inspect how things are elab'd
elab "#elab" t:term : command =>
  open Parser.Term in
  liftTermElabM do
    withoutPostponing do
    withSynthesize do
    withoutErrToSorry do
    withDeclName `lol do

    let x ← Elab.Term.elabTerm t none
    let xType ← inferType x
    let x ← Elab.Term.ensureHasType xType x
    let x ← instantiateMVars x

    IO.println s!"({repr x}) : ({repr xType})"

    IO.println s!"({←ppExpr x}) : ({←ppExpr xType})"

def Nat.repeatM [Monad m] (f : α → m α) (n : ℕ) : α → m α := n.repeat (· >>= f) ∘ pure

namespace Datadef.Command

section
  open Lean.Parser Lean.Parser.Command

  def inductive_like (cmd : String) : Parser
    := leading_parser cmd >> declId  >> ppIndent optDeclSig >> declVal

  /- "def " >> recover declId skipUntilWsOrDelim >> ppIndent optDeclSig >> declVal >> optDefDeriving -/

  def datadef := inductive_like "ddef "
  def codatadef := inductive_like "codef "

  @[command_parser]
  def declaration : Parser
    := leading_parser declModifiers false >> (datadef <|> codatadef)
end

partial def findCalls : Term → List Term
  | x@⟨.node _ ``Lean.Parser.Term.app body⟩ => x :: (body.map (findCalls ⟨·⟩)).toList.join
  | ⟨.node _ _ body⟩ => (body.map (findCalls ⟨·⟩)).toList.join
  | ⟨.missing⟩ => []
  | ⟨.atom _ _ ⟩ => []
  | ⟨.ident _ _ _ _⟩ => []

partial def getArgTypes (v : Term) : List Term := match v.raw with
  | .node _ ``Lean.Parser.Term.arrow #[arg, _, deeper] =>
     ⟨arg⟩ :: getArgTypes ⟨deeper⟩
  | rest => [⟨rest⟩]

partial def getAppNameAndArity : Term → Option (Name × ℕ)
  | ⟨.ident _ _ nm _⟩ => some (nm, 0)
  | ⟨.node _ ``Lean.Parser.Term.app #[body, _]⟩ => do
    let ⟨nm, arity⟩ ← getAppNameAndArity ⟨body⟩
    pure ⟨nm, arity.succ⟩
  | _ => none

open Parser.Term in
abbrev bb            : Parser.Parser := bracketedBinder
open Parser.Term in
instance : Coe (TSyntax ``bb) (TSyntax ``bracketedBinder)      where coe x := ⟨x.raw⟩

open Parser.Term in
def bvToFb (curr : BView) : Lean.Elab.Term.TermElabM (TSyntax ``bracketedBinder) := match curr.bi with
  | .default =>         `(bb| ( $(curr.id) : $(curr.type) ) )
  | .implicit =>        `(bb| { $(curr.id) : $(curr.type) } )
  | .strictImplicit =>  `(bb| ⦃ $(curr.id) : $(curr.type) ⦄ )
  | .instImplicit =>    `(bb| [ $(curr.id) : $(curr.type) ] )

abbrev CtorsMap := HashMap Name Name

structure TransCfg where
  (constructors : CtorsMap)
  (view : DataDefView)
  (recIdx : ℕ)

  (typeArity : ℕ)

  (ns : Name)

  (srcTy dtTy : Expr)

  (bvarTypes : List Expr)

-- TODO: Wont work for 1) Dead vars 2) higher universe types
def typeIsType : Expr → Bool := Expr.isType0

section
/- variable () -/

def transformForInfer (bvars : List Expr) (skip : ℕ) : Expr → TermElabM Expr
  | .app a b => return .app (←transformForInfer bvars skip a) (←transformForInfer bvars skip b)
  | .proj nm id s => return .proj nm id (←transformForInfer bvars skip s)
  | .mdata data a => return .mdata data (←transformForInfer bvars skip a)
  | .letE declName type value body nonDep =>
    return .letE declName (←transformForInfer bvars skip type) (←transformForInfer bvars skip value) (←transformForInfer bvars skip.succ body) nonDep
  | .forallE name type body info =>
    return .forallE name (←transformForInfer bvars skip type) (←transformForInfer bvars skip.succ body) info
  | .lam name type body info =>
    return .lam name (←transformForInfer bvars skip type) (←transformForInfer bvars skip.succ body) info
  | x@(.bvar n) => do
    if n < skip then pure x else
      let some ty := bvars.get? (n - skip) | throwError "bvar not found in safe expr extraction"
      mkFreshExprMVar (some ty)
  | x@(.const _ _) | x@(.sort _) | x@(.mvar (MVarId.mk _)) | x@(.fvar (FVarId.mk _)) | x@(.lit _) => pure x

-- Does this exist somewhere?
def safeInfer (conf : TransCfg) (e : Expr) : TermElabM Expr := do inferType (←transformForInfer conf.bvarTypes 0 e)

example : (x : ℕ) × (y : ℕ) × Fin x := ⟨10, 0, 1⟩
example : (x : ℕ) × (y : ℕ) × Fin x := Sigma.mk 10 (Sigma.mk 0 1)

#check Sigma.mk
#elab (⟨10, ()⟩ : (a : ℕ) × Unit)

def unify (a b : TermElabM Expr) (msg : String) : TermElabM Unit := do
  let a ← a
  let b ← b
  let .true ← isDefEq a b | throwError s!"Error in unification: {msg}\nUnification targets was {←ppExpr a} ∩ {←ppExpr b}"

def recallConstructor (conf : TransCfg) (id : MVarId) : Expr → TermElabM Unit
  | x@(.app a b) => do
    trace[QPF] s!"|- arg     {←ppExpr $ ←id.getType}\n               {←ppExpr x}"
    let lhs ← mkFreshExprMVar none
    let rhs ← mkFreshExprMVar none

    let deeper ← mkFreshExprMVar (some lhs)
    let deeperId := deeper.mvarId!

    let u0 ← mkFreshLevelMVar
    let u1 ← mkFreshLevelMVar

    let ty := mkApp2 (.const ``Sigma [u0, u1]) lhs rhs
    match ← isDefEq (←id.getType) ty with
    | .true =>
      recallConstructor conf deeperId a
      /- let .true ← isDefEq (.app rhs deeper) (←safeInfer conf b) | throwError "Failed to unify arg ty {←ppExpr (←safeInfer conf b)} with {←ppExpr (.app rhs deeper)}" -/
      let expr := mkApp4 (.const ``Sigma.mk [u0, u1]) lhs rhs deeper b

      unify id.getType (safeInfer conf expr) "non-final arg unification failed"

      id.assign expr
    | .false =>
      unify id.getType (safeInfer conf b) "final arg unification failed"
      id.assign b
  | _ => unreachable! -- See the precondition for when this function is called

-- Can be made terminating using gas but not really that necacerry now
partial def muncher (conf : TransCfg) (id : MVarId) (simpleArgs : List Expr) (expr : Expr) : TermElabM Unit := do
  if let .true ← isDefEq (←safeInfer conf expr) (←id.getType) then
    trace[QPF] s!"|- escape  {←ppExpr $ ←id.getType}\n               {←ppExpr expr}"
    id.assign expr
    return

  let deeperTyMVar ← mkFreshExprMVar none
  let recallTyMVar ← mkFreshExprMVar none
  let e := (mkApp2 (.const ``MvQPF.DTSum [0]) recallTyMVar deeperTyMVar)

  if ←isDefEq e (←id.getType) then
    let cont e := do
      trace[QPF] s!"|- deeper  {←ppExpr $ ←id.getType}\n               {←ppExpr e}"

      let contMVar ← mkFreshExprMVar $ some deeperTyMVar
      let contMVarId := contMVar.mvarId!

      let expr := mkApp3 (.const ``MvQPF.DTSum.cont [0]) recallTyMVar deeperTyMVar contMVar

      unify (inferType expr) id.getType "Failed to decend deeper into expression"

      muncher conf contMVarId [] e
      id.assign expr

    match expr with
    | x@(.app a _) =>
      let rec nm | .app v _ => nm v | x => x
      let nm := nm a
      if nm == .bvar conf.recIdx then
        -- precondition: If this is the case then we know the structure is a series of apps then a bvar
        let extractionPoint ← mkFreshExprMVar $ some recallTyMVar
        let extractionPointId := extractionPoint.mvarId!

        recallConstructor conf extractionPointId x

        let expr := mkApp3 (.const ``MvQPF.DTSum.recall [0]) recallTyMVar deeperTyMVar extractionPoint
        unify (inferType expr) id.getType "Failed to decend deeper into expression"

        trace[QPF] s!"assigned constructor {←ppExpr extractionPoint}"
        id.assign expr
      else cont x
    | x@(.bvar n) =>
      if n = conf.recIdx then
        trace[QPF] s!"|- bvar    {←ppExpr $ ←id.getType}\n               {←ppExpr x}"
        let expr := mkApp3 (.const ``MvQPF.DTSum.recall [0]) (.const ``Unit []) deeperTyMVar (.const ``Unit.unit [])

        unify (inferType expr) id.getType "Used recursive call like unit recall but correct type is non unit"
        trace[QPF] "Inserted unit recall point"

        id.assign expr
      else cont $ .bvar n
    | e => cont e
  else
    let tryInjExit exprTy expr := do
      trace[QPF] "Attempting injection"
      unify (pure exprTy) (pure conf.srcTy) "Failed to unify {←ppExpr exprTy} with {←ppExpr conf.srcTy} in {←ppExpr expr}"
      unify id.getType (pure conf.dtTy) "Goal type {←ppExpr (←id.getType)} failed to unify with {←ppExpr conf.dtTy} when trying injection"

      let e ← conf.typeArity.repeatM (return .app · (←mkFreshExprMVar none)) (.const (conf.ns ++ `DeepThunk.inj) [])
      let e := mkApp2 e (←mkFreshExprMVar none) expr
      unify id.getType (inferType e) "Failed to unify injection"
      id.assign e

      trace[QPF] "Injection successful {←ppExpr e} with type {←ppExpr $ ←inferType e}"

    match expr with
    | x@(.app a b) => 
      trace[QPF] s!">- app     {←ppExpr $ ←id.getType}\n               {←ppExpr x}"
      let mut x := .false
      try x := typeIsType (←inferType b) catch _ => pure ()

      if x then
        muncher conf id (b :: simpleArgs) a
      else
        let bname    ← mkFreshBinderName
        let  fnAMVar ← mkFreshExprMVar none

        let aMVar    ← mkFreshExprMVar (type? := some (.forallE bname fnAMVar (← id.getType) .default))
        let aMVarId := aMVar.mvarId!
        let bMVar    ← mkFreshExprMVar (some fnAMVar)
        let bMVarId := bMVar.mvarId!

        let expr := .app aMVar bMVar
        unify (inferType expr) id.getType "unreachable"
        id.assign expr

        muncher conf aMVarId [] a
        unify (inferType expr) id.getType "Failed to unify lhs with full application"
        muncher conf bMVarId [] b

    | .proj nm id s => throwError "unimplemented prj"
    | .mdata data a => throwError "todo"
    | .letE declName type value body nonDep => throwError "unimplemented letE"
    | .forallE name type body info => throwError "unimplemented forallE"
    | x@(.lam name _ body info) =>
      trace[QPF] s!">- lam     {←ppExpr $ ←id.getType}\n               {←ppExpr x}"
      let mVar    ← mkFreshExprMVar none
      let mVarId := mVar.mvarId!

      let tyMVar    ← mkFreshExprMVar none

      let expr := .lam name tyMVar mVar info

      id.assign expr
      unify (inferType expr) id.getType "unreachable"

      muncher ({ conf with bvarTypes := tyMVar :: conf.bvarTypes }) mVarId [] body

    | x@(.const name uls) =>
      trace[QPF] s!">- const   {←ppExpr $ ←id.getType}\n               {←ppExpr x}"
      let env ← getEnv
      let some v := env.find? name | throwError "Failed to gather constant info"

      let mkApp  := (simpleArgs.foldl (Expr.app · ·) ·)
      let consWithApps := mkApp x

      match ← isDefEq v.type (← id.getType) with
      | .true =>
        trace[QPF] s!"Selected base const: {name}"
        id.assign consWithApps
      | .false =>
        let some newCtor := conf.constructors.find? name | tryInjExit (←inferType x) x
        let expr := .app (mkApp (Expr.const newCtor [])) (← (mkFreshExprMVar none))

        unify id.getType (inferType expr) "Failed to unify new DeepThunk constructor with target"

        id.assign expr
        trace[QPF] s!"Selected const: {newCtor}"

    | x@(.bvar n) =>
      trace[QPF] s!">- bvar    {←ppExpr $ ←id.getType}\n               {←ppExpr x}"
      if n = conf.recIdx then
        throwError "TODO: make this handle unguarded corec points correctly"
        /- /- throwError "un" -/ -/
        /- if config.recIdx = 0 then pure ⟨.app (.const ``Sum.inr []) (.const ``Unit []), config⟩ -/
        /- else throwError "Should have been handled in app" -/
      else
        let some ty := conf.bvarTypes[n]? | unreachable!
        unify (pure ty) id.getType "Failed to unify bound variable with expected type"
        id.assign $ .bvar n
        trace[QPF] "bvar unified"
    | x@(.sort _) | x@(.mvar (MVarId.mk _)) | x@(.fvar (FVarId.mk _)) | x@(.lit _) =>
      throwError "sorry"
      /- handleNonRec config x -/

end

partial def addDeepThunkToConstructorName : Syntax → TermElabM Syntax
  | .ident info  rawVal  val  preresolved => return .ident info rawVal (val ++ `DeepThunk) preresolved
  /- | .node nm => sorry -/
  | .node info ``Lean.Parser.Term.app #[a, b] => return .node info ``Lean.Parser.Term.app #[←addDeepThunkToConstructorName a, b]
  | _ => throwError "Unexpected type form"

def mkRecTypes (type : Term) (view : DataDefView) : TermElabM (Term) := do
  let recTy ← view.binders.reverse.foldlM (fun accum curr => do
    let v ← bvToFb curr
    `($v:bracketedBinder → $accum)
    ) type
  let ty ← `(($recTy) → $recTy)

  return ty

#check Sigma.mk
#elab (n : ℕ) × Fin n

def mkRecCallTy (binders : Array BView) : TermElabM Term := do
  match binders.reverse.data with
  | .nil =>
    let out ← `(Unit)
    return out
  | .cons hd tl =>
    tl.foldlM (fun acc curr => `(($(curr.id):ident : $(curr.type)) × $acc)) hd.type

open Parser.Term in
@[command_elab declaration]
def elabData : CommandElab := fun stx => do
  let modifiers ← elabModifiers stx[0]
  let decl := stx[1]

  let view ← ddefSyntaxToView modifiers decl

  if view.kind = .DDef then throwErrorAt stx "ddef not yet supported"

  let some type := view.type? | throwErrorAt view.ref "Expected return type"
  let some retTy := (getArgTypes type).getLast? | throwErrorAt type "Expected return type"

  let some ⟨ns, typeArity⟩ := getAppNameAndArity retTy | throwErrorAt type "Expected return type to be coinductive"

  let env ← getEnv

  let body ← match view.value with
    | .node _ ``Lean.Parser.Command.declValSimple #[_, v, _, _] => pure v
    | _ => throwError "unimplemented"

  let constructors := env.constants.toList.foldl (fun acc ⟨nm, info⟩ =>
    match info with
    | .ctorInfo _ =>
      if (ns ++ `Shape.HeadT).isPrefixOf nm then acc
      else acc.insert
        (nm.replacePrefix (ns ++ `Shape) ns)
        (nm.replacePrefix (ns ++ `Shape) (ns ++ `DeepThunk))
    | _ => acc) HashMap.empty

  let main : TermElabM Unit := do
    let recName ← mkFreshBinderName
    let recId := mkIdent recName
    let old := mkIdent view.shortDeclName
    let body := Replace.replaceAllStx old recId body

    let some type := view.type? | throwErrorAt view.ref "Expected type"

    let recIdx := view.binders.size

    let recallTy ← mkRecCallTy view.binders
    let dtType ← `($(⟨← addDeepThunkToConstructorName type⟩):term $recallTy)

    let srcTy ← elabTerm type none
    let dtTy ← elabTerm dtType none

    let fullTy   ← mkRecTypes   type view
    let fullDtTy ← mkRecTypes dtType view

    let binders ← view.binders.mapM fun x => `(funBinder| $(⟨x.id⟩):ident)

    let stx  ← `(fun ($recId:ident) $binders* => $(⟨body⟩))
    let type ← Elab.Term.elabTerm fullTy none

    let mVar    ← mkFreshExprMVar none
    let mVarId := mVar.mvarId!

    let dtTypeE ← elabTerm fullDtTy none

    let .true ← isDefEq (← mVarId.getType) dtTypeE | throwError "Failed to unify"

    let body ← Elab.Term.elabTerm stx (some type)

    muncher ({
      constructors
      view

      typeArity

      ns

      srcTy
      dtTy

      recIdx
      bvarTypes := []
    }) mVarId [] body

    trace[QPF] "Result: {←ppExpr mVar}"

    pure ()

  liftTermElabM $ withoutPostponing $ withSynthesize $ withoutErrToSorry $ withDeclName view.declName main


end Datadef.Command


