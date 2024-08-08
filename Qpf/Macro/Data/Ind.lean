import Mathlib.Data.QPF.Multivariate.Constructions.Fix
import Mathlib.Data.QPF.Multivariate.Constructions.Cofix

import Qpf.Qpf.Multivariate.Constructions.DeepThunk
import Qpf.Macro.Data.Constructors
import Qpf.Macro.Data.RecForm
import Qpf.Macro.Data.View
import Qpf.Macro.Common
import Qpf.Util.Vec

open Lean.Parser (Parser)
open Lean Meta Elab.Command Elab.Term Parser.Term
open Lean.Parser.Tactic (inductionAlt)



def flattenForArg (n : Name) := Name.str .anonymous $ n.toStringWithSep "_" true

/-- Both `bracketedBinder` and `matchAlts` have optional arguments,
which cause them to not by recognized as parsers in quotation syntax
(that is, ``` `(bracketedBinder| ...) ``` does not work).
To work around this, we define aliases that force the optional argument to it's default value, 
so that we can write ``` `(bb| ...) ```instead. -/
abbrev bb            : Parser := bracketedBinder
abbrev matchAltExprs : Parser := matchAlts

/- Since `bb` and `matchAltExprs` are aliases for `bracketedBinder`, resp. `matchAlts`,
we can safely coerce syntax of these categories  -/
instance : Coe (TSyntax ``bb) (TSyntax ``bracketedBinder)      where coe x := ⟨x.raw⟩
instance : Coe (TSyntax ``matchAltExprs) (TSyntax ``matchAlts) where coe x := ⟨x.raw⟩

section
variable {m} [Monad m] [MonadQuotation m] [MonadError m] [MonadTrace m] [AddMessageContext m]

/-- Generate the binders for the different recursors -/
def mkRecursorBinder
    (rec_type : Term) (name : Name)
    (form : List RecursionForm)
    (inclMotives : Bool) : m (TSyntax ``bracketedBinder) := do
  let form ← form.mapM fun x => (x, mkIdent ·) <$> mkFreshBinderName
  let form := form.reverse

  let out := Syntax.mkApp (← `(motive)) #[Syntax.mkApp (mkIdent name) (form.map Prod.snd).toArray.reverse]
  let out ←
    if inclMotives then
      (form.filter (·.fst == .directRec)).foldlM (fun acc ⟨_, name⟩ => `(motive $name → $acc)) out
    else pure out

  let ty ← form.foldlM (fun acc => (match · with
    | ⟨.nonRec x, name⟩ => `(($name : $x) → $acc)
    | ⟨.directRec, name⟩ => `(($name : $rec_type) → $acc)
    | ⟨.composed x, _⟩ => throwErrorAt x "Cannot handle recursive forms"
  )) out

  `(bb | ($(mkIdent $ flattenForArg name) : $ty))

def toEqLenNames     (x : Array α) : m $ Array Ident := x.mapM (fun _ => mkIdent <$> mkFreshBinderName)
def listToEqLenNames (x : List α)  : m $ Array Ident := toEqLenNames x.toArray

/-- If the array is a singleton then this can be yielded by the proof,
otherwise it will be a n-ary product  -/
def wrapIfNotSingle (arr : TSyntaxArray `term) : m Term :=
  if let #[s] := arr then `($s)
  else `(⟨$arr,*⟩)

/-- This function behaves like reduce but is specialized for TSyntaxes.
It is used to insert ∧s between entries -/
def seq (f : TSyntax kx → TSyntax kx → m (TSyntax kx)) : List (TSyntax kx) → m (TSyntax kx)
  | [hd] => pure hd
  | hd :: tl => do f hd (← seq f tl)
  | [] => throwError "Expected at least one value for interspersing"


def generateIndBody (ctors : Array (Name × List RecursionForm)) (includeMotive : Bool) : m $ TSyntax ``matchAlts := do
  let deeper: (TSyntaxArray ``matchAlt) ← ctors.mapM fun ⟨outerCase, form⟩ => do
    let callName := mkIdent $ flattenForArg outerCase
    let outerCaseId := mkIdent $ `Shape ++ outerCase
    let rec_count := form.count .directRec

    let names ← listToEqLenNames form

    if 0 = rec_count || !includeMotive then
      return ← `(matchAltExpr| | $outerCaseId $names*, ih => ($callName $names*))

    let names ← toEqLenNames names

    let recs := names.zip (form.toArray)
          |>.filter (·.snd == .directRec)
          |>.map Prod.fst

    let cases: TSyntaxArray _ ← ctors.mapM fun ⟨innerCase, _⟩ => do
      let innerCaseTag := mkIdent innerCase
      if innerCase != outerCase then
        `(inductionAlt| | $innerCaseTag:ident => contradiction)
      else
        let split : Array (TSyntax `tactic) ← recs.mapM fun n =>
          `(tactic|rcases $n:ident with ⟨_, $n:ident⟩)
        let injections ← toEqLenNames names

        `(inductionAlt| | $innerCaseTag:ident $[$names:ident]* => (
            $split:tactic*
            injection proof with $injections*
            subst $injections:ident*
            exact $(← wrapIfNotSingle recs)
        ))

    let witnesses ← toEqLenNames recs
    let proofs ← wrapIfNotSingle witnesses
    let type ← seq (fun a b => `($a ∧ $b)) (← recs.mapM fun x => `(motive $x)).toList

    `(matchAltExpr|
      | $outerCaseId $names*, ih =>
        have $proofs:term : $type := by
          simp only [
            $(mkIdent ``MvFunctor.LiftP):ident,
            $(mkIdent ``TypeVec.PredLast):ident,
            $(mkIdent ``Fin2.instOfNatFin2HAddNatInstHAddInstAddNatOfNat):ident
          ] at ih

          rcases ih with ⟨w, proof⟩
          cases w with
          $cases:inductionAlt*
        $callName $names* $witnesses*
    )

  `(matchAltExprs| $deeper:matchAlt* )

def generateRecBody (ctors : Array (Name × List RecursionForm)) (includeMotive : Bool) : m $ TSyntax ``matchAlts := do
  let deeper: (TSyntaxArray ``matchAlt) ← ctors.mapM fun ⟨outerCase, form⟩ => do
    let callName := mkIdent $ flattenForArg outerCase
    let outerCaseId := mkIdent $ `Shape ++ outerCase

    let names ← listToEqLenNames form
    let names := names.zip form.toArray

    let desArgs ← names.mapM fun ⟨nm, f⟩ =>
      match f with
      | .directRec => `(⟨_, $nm⟩)
      | .nonRec _  => `(_)
      | .composed _ => throwError "Cannot handle composed"

    let nonMotiveArgs ← names.mapM fun _ => `(_)
    let motiveArgs    ← if includeMotive then
        names.filterMapM fun ⟨nm, f⟩ =>
        match f with
        | .directRec => some <$> `($nm)
        | .nonRec _  => pure none
        | .composed _ => throwError "Cannot handle composed"
      else pure #[]


    `(matchAltExpr|
      | $outerCaseId $desArgs* =>
        $callName $nonMotiveArgs* $motiveArgs*
    )

  `(matchAltExprs| $deeper:matchAlt*)

def createVecForArgs : Array Ident → m Term 
  | ⟨.nil⟩ => `($(mkIdent ``Vec.nil))
  | ⟨.cons hd tl⟩ => do `( ($(mkIdent ``TypeVec.append1) $(←createVecForArgs ⟨tl⟩) $hd) )

section

variable (view : DataView) (shape : Name)

def genForData : CommandElabM Unit := do
  let rec_type := view.getExpectedType

  let mapped := view.ctors.map (RecursionForm.extractWithName view.declName · rec_type)

  let ih_types ← mapped.mapM fun ⟨name, base⟩ =>
    mkRecursorBinder (rec_type) (name) base true

  let indDef : Command ← `(
    @[elab_as_elim, eliminator]
    def $(view.shortDeclName ++ `ind |> mkIdent):ident
      { motive : $rec_type → Prop}
      $ih_types*
      : (val : $rec_type) → motive val
    :=
      $(mkIdent ``_root_.MvQPF.Fix.ind)
        ($(mkIdent `p) := motive)
        (match ·,· with $(← generateIndBody mapped true)))

  let recDef : Command ← `(
    @[elab_as_elim]
    def $(view.shortDeclName ++ `rec |> mkIdent):ident
      { motive : $rec_type → Type _}
      $ih_types*
      : (val : $rec_type) → motive val
    := $(mkIdent ``MvQPF.Fix.drec)
        (match · with $(← generateRecBody mapped true)))

  let casesOnTypes ← mapped.mapM fun ⟨name, base⟩ =>
    mkRecursorBinder (rec_type) (name) base false

  let casesDef : Command ← `(
    @[elab_as_elim]
    def $(view.shortDeclName ++ `cases |> mkIdent):ident
      { motive : $rec_type → Prop}
      $casesOnTypes*
      : (val : $rec_type) → motive val
    := $(mkIdent ``_root_.MvQPF.Fix.ind)
        ($(mkIdent `p) := motive)
        (match ·,· with $(← generateIndBody mapped false)))

  let casesTypeDef : Command ← `(
    @[elab_as_elim]
    def $(view.shortDeclName ++ `casesType |> mkIdent):ident
      { motive : $rec_type → Type}
      $casesOnTypes*
      : (val : $rec_type) → motive val
    := $(mkIdent ``_root_.MvQPF.Fix.drec)
        (match · with $(← generateRecBody mapped false)))

  trace[QPF] "Rec definitions:"
  trace[QPF] indDef
  trace[QPF] recDef
  Elab.Command.elabCommand indDef
  Elab.Command.elabCommand recDef

  trace[QPF] casesDef
  trace[QPF] casesTypeDef
  Elab.Command.elabCommand casesDef
  Elab.Command.elabCommand casesTypeDef

  pure ()

def genForCoData : CommandElabM Unit := do
  if view.deadBinders.size != 0 then
    throwError "dead corecursion not supported"

  let corecType := view.getExpectedType

  let base := view.shortDeclName ++ `Base |> mkIdent

  let corecDef : Command ← `(
    def $(view.shortDeclName ++ `corec |> mkIdent):ident
        { β }
        (f : β → $(view.getExpectedTypeWithId base) β)
        : β → $corecType
      := $(mkIdent ``MvQPF.Cofix.corec) f)

  let binders : Array Ident := (← view.liveBinders.mapM fun
      | `(_) => mkIdent <$> mkFreshBinderName
      | v => pure ⟨v⟩).reverse


  let vec ← createVecForArgs binders

  let idTyFunCurried := mkIdent ``TypeFun.curried
  let idDeepThunk := mkIdent ``MvQPF.DeepThunk
  let idTyFunCurriedAux := mkIdent ``TypeFun.curriedAux
  let idRevArgs := mkIdent ``TypeFun.reverseArgs

  let dtId := view.shortDeclName ++ `DeepThunk |> mkIdent

  let deepThunk ← `(command|
    abbrev $dtId:ident :=
      $idDeepThunk $(view.shortDeclName ++ `Base.Uncurried |> mkIdent))

  let tCurr := view.getExpectedType
  let tUncurr ← `($(view.shortDeclName ++ `Uncurried |> mkIdent) $vec)
  let dtCurr ← `($(view.getExpectedTypeWithId dtId) ζ)
  let dtUncurr ← `( $(``MvQPF.DeepThunk.Uncurried |> mkIdent)
    $(view.shortDeclName ++ `Base.Uncurried |> mkIdent)
    ($(mkIdent ``TypeVec.append1) $vec ζ))

  let uncA := view.shortDeclName ++ `Unc |> mkIdent
  let uncDtA := view.shortDeclName ++ `DeepThunk.Unc |> mkIdent
  let injName := view.shortDeclName ++ `DeepThunk.inj |> mkIdent

  let curryUncurryEq ← `(command|
    theorem $uncA :
        $tCurr = $tUncurr := by
        simp only [
          $(view.shortDeclName |> mkIdent):ident,
          $idTyFunCurried:ident,
          $idTyFunCurriedAux:ident,
          $idRevArgs:ident
        ]
        congr
        funext x
        congr
        fin_cases x <;> rfl
      )
  let curryUncurryDeepThunkEq ← `(command|
    theorem $uncDtA {ζ} :
         $dtCurr = $dtUncurr
          := by
        simp only [
          $dtId:ident,
          $idDeepThunk:ident,
          $idTyFunCurried:ident,
          $idTyFunCurriedAux:ident,
          $idRevArgs:ident
        ]
        congr
        funext x
        congr
        fin_cases x <;> rfl
      )

  let Coe := mkIdent ``Coe
  let lu : Lean.Syntax.Command ← `(
    instance : $Coe ($tCurr) ($tUncurr) :=
      ⟨fun x => by rw [←$uncA]; exact x⟩
  )
  let ru : Lean.Syntax.Command ← `(
    instance : $Coe ($tUncurr) ($tCurr) :=
      ⟨fun x => by rw [$uncA:ident]; exact x⟩
  )
  let lud : Lean.Syntax.Command ← `(
    instance {ζ}: $Coe ($dtCurr) ($dtUncurr) :=
      ⟨fun x => by rw [←$uncDtA]; exact x⟩

  )
  let rud : Lean.Syntax.Command ← `(
    instance {ζ}: $Coe ($dtUncurr) ($dtCurr) :=
      ⟨fun x => by rw [$uncDtA:ident]; exact x⟩
  )
  let injDef : Lean.Syntax.Command ← `(
    def $injName {ζ} (x : $tCurr) : $dtCurr :=
        let x : $tUncurr := x
        let x : $dtUncurr := $(mkIdent ``MvQPF.DeepThunk.inject) x
        x
  )
  let inj : Lean.Syntax.Command ← `(
    instance {ζ}: $Coe ($tCurr) ($dtCurr) := ⟨$injName⟩
  )
  let dtCorec : Lean.Syntax.Command ← `(
    def $(view.shortDeclName ++ `DeepThunk.corec |> mkIdent) { ζ } (f : ζ → $dtCurr) (v : ζ) : $tCurr :=
      let v : $tUncurr := $(mkIdent ``MvQPF.DeepThunk.corec) (fun v => f v) v
      v
  )

  trace[QPF] "Corec definitions:"
  trace[QPF] corecDef
  trace[QPF] deepThunk
  trace[QPF] curryUncurryEq
  trace[QPF] curryUncurryDeepThunkEq

  trace[QPF] lu
  trace[QPF] ru
  trace[QPF] lud
  trace[QPF] rud
  trace[QPF] inj

  trace[QPF] dtCorec

  elabCommand corecDef
  elabCommand deepThunk
  elabCommand curryUncurryEq
  elabCommand curryUncurryDeepThunkEq

  elabCommand lu
  elabCommand ru
  elabCommand lud
  elabCommand rud
  elabCommand injDef
  elabCommand inj

  elabCommand dtCorec


  Data.Command.mkConstructorsWithNameAndType view shape (fun ctor =>
    (view.shortDeclName ++ `DeepThunk ++ (ctor.declName.replacePrefix view.declName .anonymous) |> mkIdent))
    (← `($(mkIdent ``MvQPF.DTSum) ζ ($dtCurr)))
    dtCurr
    (#[(← `(bb|{ ζ : Type }) : TSyntax ``bracketedBinder)])

def genRecursors : CommandElabM Unit := match view.command with
  | .Data => genForData view
  | .Codata => genForCoData view shape

end
end

