import Qpf.Macro.Data.View
import Qpf.Macro.Common
import Mathlib.Data.QPF.Multivariate.Constructions.Fix
import Mathlib.Tactic.ExtractGoal

open Lean.Parser (Parser)
open Lean Meta Elab.Command Elab.Term Parser.Term
open Lean.Parser.Tactic (inductionAlt)

/--
  The recursive form encodes how a function argument is recursive.

  Examples ty R α:

   α      → R α       → List (R α) → R α
  [nonRec,  directRec,  composed        ]
-/
inductive RecursionForm :=
  | nonRec (stx: Term)
  | directRec
  -- | composed -- Not supported yet
deriving Repr, BEq

partial def getArgTypes (v : Term) : List Term := match v.raw with
  | .node _ ``arrow #[arg, _, deeper] =>
     ⟨arg⟩ :: getArgTypes ⟨deeper⟩
  | rest => [⟨rest⟩]

def flattenForArg (n : Name) := Name.str .anonymous $ n.toStringWithSep "_" true

def containsStx (top : Term) (search : Term) : Bool :=
  (top.raw.find? (· == search)).isSome

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

/-- When we want to operate on patterns the names we need must start with shape.
This is done as if theres a constructor called `mk` dot notation breaks. -/
def addShapeToName : Name → Name
  | .anonymous => .str .anonymous "Shape"
  | .str a b => .str (addShapeToName a) b
  | .num a b => .num (addShapeToName a) b

section
variable {m} [Monad m] [MonadQuotation m] [MonadError m] [MonadTrace m] [AddMessageContext m]

/-- Extract takes a constructor and extracts its recursive forms.

This function assumes the pre-processor has run
It also assumes you don't have polymorphic recursive types such as
data Ql α | nil | l : α → Ql Bool → Ql α -/
def extract (topName : Name) (view : CtorView) (rec_type : Term) : m $ Name × List RecursionForm :=
  (view.declName.replacePrefix topName .anonymous , ·) <$> (do
  let some type := view.type? | pure []
  let type_ls := (getArgTypes ⟨type⟩).dropLast

  type_ls.mapM fun v =>
    if v == rec_type then pure .directRec
    else if containsStx v rec_type then
        throwErrorAt v.raw "Cannot handle composed recursive types"
    else pure $ .nonRec v)

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
    let outerCaseId := mkIdent $ addShapeToName outerCase
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
    let outerCaseId := mkIdent $ addShapeToName outerCase

    let names ← listToEqLenNames form
    let names := names.zip form.toArray

    let desArgs ← names.mapM fun ⟨nm, f⟩ =>
      match f with
      | .directRec => `(⟨_, $nm⟩)
      | .nonRec _  => `(_)

    let nonMotiveArgs ← names.mapM fun _ => `(_)
    let motiveArgs    ← if includeMotive then
        names.filterMapM fun ⟨nm, f⟩ =>
        match f with
        | .directRec => some <$> `($nm)
        | .nonRec _  => pure none
      else pure #[]


    `(matchAltExpr|
      | $outerCaseId $desArgs* =>
        $callName $nonMotiveArgs* $motiveArgs*
    )

  `(matchAltExprs| $deeper:matchAlt*)

def genRecursors (view : DataView) : CommandElabM Unit := do
  let rec_type := view.getExpectedType

  let mapped ← view.ctors.mapM (extract view.declName · rec_type)

  let ih_types ← mapped.mapM fun ⟨name, base⟩ =>
    mkRecursorBinder (rec_type) (name) base true

  let indDef : Command ← `(
    @[elab_as_elim, eliminator]
    def $(.str view.shortDeclName "ind" |> mkIdent):ident
      { motive : $rec_type → Prop}
      $ih_types*
      : (val : $rec_type) → motive val
    :=
      $(mkIdent ``_root_.MvQPF.Fix.ind)
        ($(mkIdent `p) := motive)
        (match ·,· with $(← generateIndBody mapped true)))

  let recDef : Command ← `(
    @[elab_as_elim]
    def $(.str view.shortDeclName "rec" |> mkIdent):ident
      { motive : $rec_type → Type _}
      $ih_types*
      : (val : $rec_type) → motive val
    := $(mkIdent ``MvQPF.Fix.drec)
        (match · with $(← generateRecBody mapped true)))

  let casesOnTypes ← mapped.mapM fun ⟨name, base⟩ =>
    mkRecursorBinder (rec_type) (name) base false

  let casesDef : Command ← `(
    @[elab_as_elim]
    def $(.str view.shortDeclName "cases" |> mkIdent):ident
      { motive : $rec_type → Prop}
      $casesOnTypes*
      : (val : $rec_type) → motive val
    := $(mkIdent ``_root_.MvQPF.Fix.ind)
        ($(mkIdent `p) := motive)
        (match ·,· with $(← generateIndBody mapped false)))

  let casesTypeDef : Command ← `(
    @[elab_as_elim]
    def $(.str view.shortDeclName "casesType" |> mkIdent):ident
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
