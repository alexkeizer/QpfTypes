import Qpf.Macro.Data.View
import Qpf.Macro.Common
import Mathlib.Data.QPF.Multivariate.Constructions.Fix
import Mathlib.Tactic.ExtractGoal

open Lean.Parser (Parser)
open Lean Meta Elab.Command Elab.Term Parser.Term

/--
  The recursive form encodes how a function argument is recursive.

  Examples ty R α:

   α      → R α       → List (R α) → R α
  [nonRec,  directRec,  composed        ]
-/
inductive RecursionForm :=
  | nonRec (stx: Term)
  | directRec
  /- | composed -/
deriving Repr, BEq

partial def getArgTypes (v : Term) : List Term := match v.raw with
  | .node _ ``arrow #[arg, _, deeper] =>
     ⟨arg⟩ :: getArgTypes ⟨deeper⟩
  | rest => [⟨rest⟩]


def containsStx (top : Term) (search : Term) : Bool :=
  (top.raw.find? (· == search)).isSome

def ripSuffix : Name → Name
  | .str _ s => .str .anonymous s
  | _ => .anonymous -- Unhandled case

-- These parsers have to be declared as they have optional args breaking quotation
abbrev bb            : Parser := bracketedBinder
abbrev matchAltExprs : Parser := matchAlts

instance : Coe (TSyntax ``bb) (TSyntax ``bracketedBinder) where coe x := ⟨x.raw⟩
instance : Coe (TSyntax ``matchAltExprs) (TSyntax ``matchAlts) where coe x := ⟨x.raw⟩

section
variable {m} [Monad m] [MonadQuotation m] [MonadError m] [MonadTrace m] [AddMessageContext m]

-- This function assumes the pre-processor has run
-- It also assumes you don't have polymorphic recursive types such as
-- data Ql α | nil | l : α → Ql Bool → Ql α
def extract (view : CtorView) (rec_type : Term) : m $ Name × List RecursionForm :=
  (ripSuffix view.declName, ·) <$> (do
  let some type := view.type? | pure []
  let type_ls := (getArgTypes ⟨type⟩).dropLast

  let transform ← type_ls.mapM fun v =>
    if v == rec_type then pure .directRec
    else if containsStx v rec_type then
        throwErrorAt v.raw "Cannot handle composed recursive types"
    else pure $ .nonRec v

  pure transform)

def mkConstructorType (rec_type : Term) (name : Ident) (form : List RecursionForm): m (TSyntax ``bracketedBinder) := do
  let form ← form.mapM fun x => (x, mkIdent ·) <$> mkFreshBinderName
  let form := form.reverse

  let out := Syntax.mkApp (← `(motive)) #[Syntax.mkApp name (form.map Prod.snd).toArray.reverse]
  let out ← (form.filter (·.fst == .directRec)).foldlM (fun acc ⟨_, name⟩ => `(motive $name → $acc)) out

  let ty ← form.foldlM (fun acc => (match · with
    | ⟨.nonRec x, name⟩ => `(($name : $x) → $acc)
    | ⟨.directRec, name⟩ => `(($name : $rec_type) → $acc)
  )) out

  `(bb | ($name : $ty))

def toEqLenNames     (x : Array α) : m $ Array Ident := x.mapM (fun _ => mkIdent <$> mkFreshBinderName)
def listToEqLenNames (x : List α)  : m $ Array Ident := toEqLenNames x.toArray

def wrapIfNotSingle (arr : TSyntaxArray `term) : m Term :=
  if let #[s] := arr then `($s)
  else `(⟨$arr,*⟩)

def seq [Coe α (TSyntax kx)] (f : α → TSyntax kx → m (TSyntax kx)) : List α → m (TSyntax kx)
  | [hd] => pure hd
  | hd :: tl => do f hd (← seq f tl)
  | [] => pure ⟨.node .none `null #[]⟩

def generate_body (values : Array (Name × List RecursionForm)) : m $ TSyntax ``matchAlts := do
  let deeper: (TSyntaxArray ``matchAlt) ← values.mapM fun ⟨outerCase, form⟩ => do
    let outerCaseId := mkIdent outerCase
    let rec_count := form.count .directRec

    let names ← listToEqLenNames form

    if 0 = rec_count then
      return ← `(matchAltExpr| | .$outerCaseId $names*, ih => ($outerCaseId $names*))

    -- TODO: this is not a good way to deal with names
    --       but, for some unknowable reason, this fixes a shadowing
    --       issue

    let names : Array Ident := ⟨
      names.toList.enum.map fun ⟨i, _⟩ =>
        mkIdent <| Name.str (.anonymous) s!"_PRIVATE_ y {i}"
    --                                      ^^^^^^^^^^^^^^^
    -- HACK: notice how the variable name contains spaces.
    -- This is deliberate, to reduce the possibility of name collisions,
    -- given that these names are unhygienic
    ⟩
    -- The following would be better, with fresh names,
    -- but for some reason this causes the variable `p` to be renamed to something new, which will then give errors when we use `p` later on
    -- let names : Array Ident ← names.mapM fun _ => do
    --   mkFreshIdent .missing

    let recs := names.zip (form.toArray)
          |>.filter (·.snd == .directRec)
          |>.map Prod.fst

    let p := mkIdent `proof
    let w := mkIdent `witness

    let cases ← values.mapM fun ⟨innerCase, _⟩ => do
      let innerCaseTag := mkIdent innerCase
      if innerCase != outerCase then
        `(tactic| case $innerCaseTag:ident => contradiction)
      else
        let split : Array (TSyntax `tactic) ← names.mapM fun n =>
          `(tactic|rcases $n:ident with ⟨_, $n:ident⟩)
        let injections ← toEqLenNames names

        `(tactic|
          case $innerCaseTag:ident $[$names:ident]* => (
            $split:tactic*
            injection $p:ident with $injections*
            subst $injections:ident*
            exact $(← wrapIfNotSingle recs)
        ))

    let witnesses ← toEqLenNames recs
    let proofs ← wrapIfNotSingle witnesses
    let type ← seq (fun a b => `($a ∧ $b)) (← recs.mapM fun x => `(motive $x)).toList

    `(matchAltExpr|
      | .$outerCaseId $names*, ih =>
        have $proofs:term : $type := by
          simp only [
            $(mkIdent ``MvFunctor.LiftP):ident,
            $(mkIdent ``TypeVec.PredLast):ident,
            $(mkIdent ``Fin2.instOfNatFin2HAddNatInstHAddInstAddNatOfNat):ident
          ] at ih

          rcases ih with ⟨$w:ident, $p:ident⟩
          cases $w:ident
          $cases:tactic*
        $outerCaseId:ident $names* $witnesses*
    )

  `(matchAltExprs| $deeper:matchAlt* )
end


def mkInd (view : DataView) : CommandElabM Unit := do
  let rec_type := view.getExpectedType

  let mapped ← view.ctors.mapM (extract · rec_type)
  let ih_types ← mapped.mapM fun ⟨name, base⟩ =>
    mkConstructorType rec_type (mkIdent name) base

  let out: Command ← `(
    @[elab_as_elim, eliminator]
    def $(.str view.shortDeclName "ind" |> mkIdent):ident
      { motive : $rec_type → Prop}
      $ih_types*
      : (val : $rec_type) → motive val
    :=
      $(mkIdent $ ``_root_.MvQPF.Fix.ind)
        ($(mkIdent `p) := motive)
        (match ·,· with $(← generate_body mapped)))

  trace[QPF] "Recursor definition:"
  trace[QPF] out

  Elab.Command.elabCommand out

  pure ()
