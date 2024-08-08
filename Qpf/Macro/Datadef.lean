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

/- def handleNonRec (config : TransCfg) (e : Expr) : TermElabM (Expr × TransCfg) := do -/
/-   let ty ← inferType e -/

/-   if config.active ∧ (← isDefEqGuarded ty config.targetType) then -/
/-     pure ⟨.app (.const ``Sum.inl []) e, config⟩ -/
/-   else pure ⟨e, config⟩ -/

/- def transformer (config : TransCfg) : Expr → TermElabM (Expr × TransCfg) -/
/-   | x@(.app a b) => do -/
/-     /- let rec getLeftMostVal : Expr → Expr -/ -/
/-     /-   | .app l _ => getLeftMostVal l -/ -/
/-     /-   | x => x -/ -/
/-     /- let v := getLeftMostVal a -/ -/

/-     trace[QPF] (repr x) -/

/-     let ⟨a, config⟩ ← transformer config a -/
/-     let ⟨b, config⟩ ← transformer config b -/

/-     pure ⟨.app a b, config⟩ -/
/-   | .proj nm id s => throwError "unimplemented prj" -/
/-   | .mdata data a => (fun x => ⟨.mdata data x.fst, x.snd⟩) <$> transformer config a -/
/-   | .letE declName type value body nonDep => throwError "unimplemented letE" -/
/-   | .forallE name type body info => throwError "unimplemented faE" -/
/-   | .lam name type body info => -/
/-     (fun x => ⟨.lam name type x.fst info, x.snd⟩) <$> transformer config body -/
/-   | x@(.const name uls) => -/
/-     if config.returnSide then -/
/-       match config.constructors.find? name with -/
/-       | .some v => pure ⟨.const v uls, { config with active := true }⟩ -- TODO: are ULevels correct -/
/-       | .none => pure ⟨x, config⟩ -/
/-     else pure ⟨x, config⟩ -/
/-   | .bvar n => do -/
/-     if n = config.recIdx then -/
/-       /- throwError "un" -/ -/
/-       if config.recIdx = 0 then pure ⟨.app (.const ``Sum.inr []) (.const ``Unit []), config⟩ -/
/-       else throwError "Should have been handled in app" -/
/-     else pure ⟨.bvar n, config⟩ -/
/-   | x@(.sort _) | x@(.mvar (MVarId.mk _)) | x@(.fvar (FVarId.mk _)) | x@(.lit _) => do -/
/-     handleNonRec config x -/

-- TODO: Wont work for 1) Dead vars 2) higher universe types
def typeIsType : Expr → Bool := Expr.isType0

-- Can be made terminating using gas but not really that necacerry now
partial def muncher (config : TransCfg) (id : MVarId) (simpleArgs : List Expr) (expr : Expr) : TermElabM Unit := do
  -- TODO: If the type of the id and the expr are the same we can use this
  try
    if let .true ← isDefEq (←inferType expr) (←id.getType) then
      trace[QPF] s!"|- escape  {←ppExpr $ ←id.getType}\n               {←ppExpr expr}"
      id.assign expr
      return
  catch | _ => pure ()

  let deeperTyMVar ← mkFreshExprMVar none
  let e := (mkApp2 (.const ``MvQPF.DTSum [0]) (←mkFreshExprMVar none) deeperTyMVar)

  if ←isDefEq e (←id.getType) then
    let cont e := do
      trace[QPF] s!"|- deeper  {←ppExpr $ ←id.getType}\n               {←ppExpr e}"

      let contMVar ← mkFreshExprMVar $ some deeperTyMVar
      let contMVarId := contMVar.mvarId!

      let expr := mkApp3 (.const ``MvQPF.DTSum.cont [0]) (←mkFreshExprMVar none) deeperTyMVar contMVar

      let .true ← isDefEq (←inferType expr) (←id.getType) | throwError "Failed to decend deeper into expression"

      muncher config contMVarId [] e
      id.assign expr

    match expr with
    | x@(.app a b) =>
      let rec nm | .app v _ => nm v | x => x
      let nm := nm a
      if nm == .bvar config.recIdx then
        throwError "app"
      else cont x
    | x@(.bvar n) =>
      if n = config.recIdx then
        trace[QPF] s!"|- bvar    {←ppExpr $ ←id.getType}\n               {←ppExpr x}"
        let expr := mkApp3 (.const ``MvQPF.DTSum.recall [0]) (.const ``Unit []) (←mkFreshExprMVar none) (.const ``Unit.unit [])

        let .true ← isDefEq (←inferType expr) (←id.getType) | throwError "Used recursive call like unit recall but correct type is non unit"
        trace[QPF] "Inserted unit recall point"

        id.assign expr
      else cont $ .bvar n
    | e => cont e
  else
    let tryInjExit exprTy expr := do
      trace[QPF] "Attempting injection"
      let .true ← isDefEq exprTy config.srcTy       | throwError "Failed to unify {←ppExpr exprTy} with {←ppExpr config.srcTy} in {←ppExpr expr}"
      let .true ← isDefEq (←id.getType) config.dtTy | throwError "Goal type {←ppExpr (←id.getType)} failed to unify with {←ppExpr config.dtTy} when trying injection"

      let e : Expr ← config.typeArity.repeatM (return .app · (←mkFreshExprMVar none)) (.const (config.ns ++ `DeepThunk.inj) [])
      let e := mkApp2 e (←mkFreshExprMVar none) expr
      let .true ← isDefEq (←id.getType) (←inferType e) | throwError "Failed to unify injection"
      id.assign e

      trace[QPF] "Injection successful {←ppExpr e} with type {←ppExpr $ ←inferType e}"

    match expr with
    | x@(.app a b) => 
      trace[QPF] s!">- app     {←ppExpr $ ←id.getType}\n               {←ppExpr x}"
      let mut x := .false
      try x := typeIsType (←inferType b) catch _ => pure ()

      if x then
        muncher config id (b :: simpleArgs) a
      else
        let bname    ← mkFreshBinderName
        let  fnAMVar ← mkFreshExprMVar none

        let aMVar    ← mkFreshExprMVar (type? := some (.forallE bname fnAMVar (← id.getType) .default))
        let aMVarId := aMVar.mvarId!
        let bMVar    ← mkFreshExprMVar (some fnAMVar)
        let bMVarId := bMVar.mvarId!

        let expr := .app aMVar bMVar
        let .true ← isDefEq (← inferType expr) (←id.getType) | unreachable! -- Most generic choice
        id.assign expr

        muncher config aMVarId [] a
        let .true ← isDefEq (← inferType expr) (←id.getType) | throwError "failed to unify lhs with full application"
        /- let .true ← isDefEq (← inferType b) (←b.getType) | throwError "failed to unify" -/
        muncher config bMVarId [] b

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
      let .true ← isDefEq (← inferType expr) (←id.getType) | unreachable!

      muncher ({ config with bvarTypes := tyMVar :: config.bvarTypes }) mVarId [] body

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
        let some newCtor := config.constructors.find? name | tryInjExit (←inferType x) x
        let expr := .app (mkApp (Expr.const newCtor [])) (← (mkFreshExprMVar none))

        let .true ← isDefEq (←id.getType) (←inferType expr) | throwError "Failed to unify new DeepThunk constructor with target"

        id.assign expr
        trace[QPF] s!"Selected const: {newCtor}"

    | x@(.bvar n) =>
      trace[QPF] s!">- bvar    {←ppExpr $ ←id.getType}\n               {←ppExpr x}"
      if n = config.recIdx then
        throwError "TODO: make this handle unguarded corec points correctly"
        /- /- throwError "un" -/ -/
        /- if config.recIdx = 0 then pure ⟨.app (.const ``Sum.inr []) (.const ``Unit []), config⟩ -/
        /- else throwError "Should have been handled in app" -/
      else
        let some ty := config.bvarTypes[n]? | unreachable!
        let .true ← isDefEq ty (←id.getType) | throwError "Failed to unify bound variable with expected type"
        id.assign $ .bvar n
        trace[QPF] "bvar unified"
    | x@(.sort _) | x@(.mvar (MVarId.mk _)) | x@(.fvar (FVarId.mk _)) | x@(.lit _) =>
      throwError "sorry"
      /- handleNonRec config x -/


partial def addDeepThunkToConstructorName : Syntax → TermElabM Syntax
  | .ident info  rawVal  val  preresolved => return .ident info rawVal (val ++ `DeepThunk) preresolved
  /- | .node nm => sorry -/
  | .node info ``Lean.Parser.Term.app #[a, b] => return .node info ``Lean.Parser.Term.app #[←addDeepThunkToConstructorName a, b]
  | x =>
    throwError "Unexpected type form"

def mkRecTypes (type : Term) (view : DataDefView) : TermElabM (Term) := do
  let recTy ← view.binders.reverse.foldlM (fun accum curr => do
    let v ← bvToFb curr
    `($v:bracketedBinder → $accum)
    ) type
  let ty ← `(($recTy) → $recTy)

  return ty

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

    let dtType ← `($(⟨← addDeepThunkToConstructorName type⟩):term $(mkIdent `Unit))

    let srcTy ← elabTerm type none
    let dtTy ← elabTerm dtType none

    let fullTy   ← mkRecTypes   type view
    let fullDtTy ← mkRecTypes dtType view

    let binders ← view.binders.mapM fun x => `(funBinder| $(⟨x.id⟩):ident)

    let stx ← `(fun ($recId:ident) $binders* => $(⟨body⟩))
    let type ← Elab.Term.elabTerm fullTy none

    let body ← Elab.Term.elabTerm stx (some type)

    let mVar    ← mkFreshExprMVar none
    let mVarId := mVar.mvarId!

    let dtTypeE ← elabTerm fullDtTy none

    /- let recTy ← view.binders.reverse.foldlM (fun accum curr => do -/
    /-   let v ← bvToFb curr -/
    /-   `($v:bracketedBinder → $accum) -/
    /-   ) type -/
    /- let ty ← `(($recTy) → $recTy) -/

    let .true ← isDefEq (← mVarId.getType) dtTypeE | throwError "Failed to unify"


    /- let opTy  ← view.binders.foldlM (fun body curr => (.lam curr.name · body curr.bi) <$> elabTerm curr.type none) (Expr.mvar mVarId) -/
    /- let opTy := .lam recName (←elabTerm recTy none) opTy .default -/

    /- trace[QPF] ←ppExpr $ muncher config opTy -/
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

    pure ()

  liftTermElabM $ withoutPostponing $ withSynthesize $ withoutErrToSorry $ withDeclName view.declName main


end Datadef.Command

/- open Parser.Term -/
/- elab "#test" t:term : command => -/
/-   liftTermElabM do -/
/-     withoutPostponing do -/
/-     withSynthesize do -/
/-     withoutErrToSorry do -/
/-     withDeclName `lol do -/

/-     let x ← Elab.Term.elabTerm t none -/
/-     let xType ← inferType x -/
/-     let xChecked ← Elab.Term.ensureHasType xType x -/
/-     let xFinal ← instantiateMVars xChecked -/

/-     let env ← getEnv -/

/-     trace[QPF] (← ppExpr xFinal) -/
/-     trace[QPF] (repr xFinal) -/

/-     let some x := env.find? `lol.match_1 | pure () -/
/-     trace[QPF] x.type -/
/-     trace[QPF] (← ppExpr x.type) -/

/- #test (0).succ -/
