import Std.Tactic.OpenPrivate
import Mathlib.Util.WhatsNew
import Mathlib.Data.Set.Basic
import Lean

open Lean Meta Elab.Command
open Elab (Modifiers elabModifiers)
open Elab.Term (BinderView)
open Parser.Term (namedArgument)
open PrettyPrinter (delab)

namespace Coind

namespace Parser
open Lean.Parser Lean.Parser.Command

def coind : Parser :=
  leading_parser "coinductive " >> declId
                     >> Command.declSig
                     >> Lean.Parser.optional (symbol " :=" <|> " where")
                     >> many ctor
                     /- >> optDeriving -/

@[command_parser]
def declaration : Parser := leading_parser declModifiers false >> coind
end Parser

structure CoinductiveView.CtorView where
  ref       : Syntax
  modifiers : Modifiers
  declName  : Name
  binders   : Array BinderView
  type?     : Option Term
  deriving Inhabited

structure CoinductiveView : Type where
  ref             : TSyntax ``Parser.declaration
  declId          : TSyntax ``Parser.Command.declId
  modifiers       : Modifiers
  shortDeclName   : Name
  declName        : Name
  levelNames      : List Name
  binders         : Array BinderView
  type            : Term
  ctors           : Array CoinductiveView.CtorView
  /- derivingClasses : Array Lean.Elab.DerivingClassView -/
  /- computedFields  : Array Lean.Elab.Command.ComputedFieldView -/
  deriving Inhabited

namespace CoinductiveView

open private toBinderViews from Lean.Elab.Binders in
private def toBViews (stx : Syntax) : CommandElabM $ Array Elab.Term.BinderView := do
  let x ← liftTermElabM $ stx.getArgs.mapM toBinderViews
  return x.flatten

def CtorView.ofStx (declName : Name) (modifiers : Modifiers) (ref : Syntax) : CommandElabM CtorView := do
  let mut ctorModifiers ← elabModifiers ref[2]
  if let some leadingDocComment := ref[0].getOptional? then
    if ctorModifiers.docString?.isSome then
      logErrorAt leadingDocComment "duplicate doc string"
    ctorModifiers := { ctorModifiers with docString? := TSyntax.getDocString ⟨leadingDocComment⟩ }
  if ctorModifiers.isPrivate && modifiers.isPrivate then
    throwError "invalid 'private' constructor in a 'private' inductive datatype"
  if ctorModifiers.isProtected && modifiers.isPrivate then
    throwError "invalid 'protected' constructor in a 'private' inductive datatype"

  checkValidCtorModifier ctorModifiers
  let ctorName := ref.getIdAt 3
  let ctorName := declName ++ ctorName
  let ctorName ← withRef ref[3] $ Elab.applyVisibility ctorModifiers.visibility ctorName
  let (binders, type?) := Elab.expandOptDeclSig ref[4]
  addDocString' ctorName ctorModifiers.docString?
  Elab.addAuxDeclarationRanges ctorName ref ref[3]

  let binders ← toBViews binders

  return { ref, modifiers := ctorModifiers, declName := ctorName, binders, type? := type?.map (⟨·⟩) }

open private toBinderViews from Lean.Elab.Binders in
def ofStx (stx : Syntax) : CommandElabM CoinductiveView := do
  let modifiers ← elabModifiers stx[0]
  let decl := stx[1]
  let (binders, type) := Elab.expandDeclSig decl[2]!

  let binders ← toBViews binders

  let declId  := ⟨decl[1]⟩
  let ⟨shortDeclName, declName, levelNames⟩ ← expandDeclId declId.raw modifiers

  let ctors ← decl[4].getArgs.mapM $ CtorView.ofStx declName modifiers

  Lean.Elab.addDeclarationRanges declName decl

  let out := {
    ref := ⟨decl⟩

    declName
    shortDeclName

    levelNames
    type := ⟨type⟩

    binders
    ctors

    declId
    modifiers
  }

  -- TODO: Here a check should be done to ensure that the ret-type is Prop

  return out

end CoinductiveView

open Parser.Term in
section
abbrev bb            : Lean.Parser.Parser := bracketedBinder
abbrev matchAltExprs : Lean.Parser.Parser := matchAlts

/- Since `bb` and `matchAltExprs` are aliases for `bracketedBinder`, resp. `matchAlts`,
we can safely coerce syntax of these categories  -/
instance : Coe (TSyntax ``bb) (TSyntax ``bracketedBinder)      where coe x := ⟨x.raw⟩
instance : Coe (TSyntax ``matchAltExprs) (TSyntax ``matchAlts) where coe x := ⟨x.raw⟩
end

def binderViewtoBracketedBinder (v : BinderView) : CommandElabM $ TSyntax ``Parser.Term.bracketedBinder := do match v.bi with
  | .default =>        `(bb|( $(⟨v.id⟩):ident : $(⟨v.type⟩) ))
  | .implicit =>       `(bb|{ $(⟨v.id⟩):ident : $(⟨v.type⟩) })
  | .strictImplicit => `(bb|⦃ $(⟨v.id⟩):ident : $(⟨v.type⟩) ⦄)
  | .instImplicit =>   `(bb|[ $(⟨v.id⟩):ident : $(⟨v.type⟩) ])

partial def typeToArgArr (type : Term) : Array Term × Term := Prod.map List.toArray id $ go type.raw
  where go
    | Syntax.node _ ``Parser.Term.arrow #[hd, _, tail] => Prod.map (⟨hd⟩ :: ·) id $ go tail
    | rest => ⟨[], ⟨rest⟩⟩

deriving instance Repr for BinderView



def generateIs (view : CoinductiveView) : CommandElabM Unit := do
  let v : Array Term ← view.ctors.mapM ctor

  if v.size = 0 then throwErrorAt view.ref s!"{view.declName} coinductive predicate is isomorphic to False"

  let p ← v.pop.foldlM (fun acc curr => `($acc ∨ $curr)) v.back
  let stx ← `(command|
    abbrev $(view.shortDeclName ++ `Is |> mkIdent) $(←view.binders.mapM binderViewtoBracketedBinder)* ($(view.shortDeclName |> mkIdent) : $(view.type)) : Prop := $p)

  Lean.Elab.Command.elabCommand stx

  where
    ctor view := do
      let .some type := view.type? | throwErrorAt view.ref "An coinductive predicate without a retty could better be expressed inductively" -- TODO: is this the case
      let ⟨args, out⟩ := typeToArgArr type
      let ⟨inputBinders, dualizedBinders⟩ := view.binders.foldl (fun ⟨a, b⟩ v =>
        if (out.raw.find? (· == v.id)).isSome then ⟨v :: a, b⟩ else ⟨a, v :: b⟩
      ) $ Prod.mk [] []

      -- Currently, here, it assocaites the wrong way TODO: make it assocaite the right way
      let args := args.reverse
      let body ← if args.size = 0 then `(True)
        else args.pop.foldlM (fun acc curr => `($acc ∧ $curr)) args.back

      -- As ∃ is just Σ in u = 0, we represent possibly depdented values using ∃
      let body ← dualizedBinders.foldlM (fun acc curr => `(∃ $(⟨curr.id⟩):ident : $(⟨curr.type⟩):term, $acc )) body
      let body ← `(∀ $(List.toArray $ ←inputBinders.reverse.mapM binderViewtoBracketedBinder):bracketedBinder*, $out → $body)

      return body

open Macro in
@[command_elab Coind.Parser.declaration]
def elabData : CommandElab := fun stx => do
  let view ← CoinductiveView.ofStx stx

  let ⟨argArr, out⟩ := typeToArgArr view.type
  let .node _ ``Parser.Term.prop _ := out.raw | throwErrorAt out "Expected return type to be a Prop"

  let argArr := (← argArr.mapM (fun _ => Elab.Term.mkFreshBinderName)).map mkIdent

  generateIs view
  let stx ← `(
    def $(view.shortDeclName |> mkIdent) $(←view.binders.mapM binderViewtoBracketedBinder)* : $(view.type) :=
      fun $argArr* => ∃ R, @$(view.shortDeclName ++ `Is |> mkIdent) $(view.binders.map (⟨·.id⟩)):ident* R ∧ R $argArr* )
  Lean.Elab.Command.elabCommand stx
end Coind


namespace Test

structure FSM where
  S : Type
  d : S → Set S
  A : Set S

coinductive Bisim (fsm : FSM) : fsm.S → fsm.S → Prop :=
  | step {s t : fsm.S} :
    (s ∈ fsm.A ↔ t ∈ fsm.A)
    → (∀ s' ∈ fsm.d s, ∃ t' ∈ fsm.d t, Bisim s' t')
    → (∀ t' ∈ fsm.d t, ∃ s' ∈ fsm.d s, Bisim s' t')
    → Bisim s t

macro "coinduction " "using" P:term "with" ids:(ppSpace colGt ident)+ : tactic =>
  let ids := ids
  `(tactic| (exists $P; constructor; intro $ids*))

theorem bisim_refl : Bisim f a a := by
  exists fun a b => a = b
  simp only [and_true]
  intro s t seqt
  simp_all

theorem bisim_refl' : Bisim f a a := by
  coinduction using (· = ·) with s t h_Rst
  · simp [h_Rst]
  · rfl

theorem bisim_symm (h : Bisim f a b): Bisim f b a := by
  rcases h with ⟨rel, relIsBisim, rab⟩
  use fun a b => rel b a
  simp_all
  intro a₁ b₁ holds
  specialize relIsBisim holds
  simp_all only [implies_true, and_self]

theorem bisim_trans (x : Bisim f a b) (y : Bisim f b c) : Bisim f a c := by
  rcases x with ⟨wx, pix, rab⟩
  rcases y with ⟨wy, piy, rac⟩
  use fun a c => ∃ b, wx a b ∧ wy b c
  constructor
  · intro a c ⟨b, wab, wbc⟩
    specialize pix wab
    specialize piy wbc
    rcases pix with ⟨⟨aimpb, bdrivea⟩, adriveb⟩
    rcases piy with ⟨⟨bimpc, cdriveb⟩, bdrivec⟩
    simp_all only [true_and]
    constructor
    <;> intro v vmem
    · specialize cdriveb v vmem
      rcases cdriveb with ⟨wb, wbmem, rvwb⟩
      specialize bdrivea wb wbmem
      rcases bdrivea with ⟨wa, wamem, rvwa⟩
      use wa
      simp_all only [true_and]
      use wb
    · specialize adriveb v vmem
      rcases adriveb with ⟨wb, wbmem, rvwb⟩
      specialize bdrivec wb wbmem
      rcases bdrivec with ⟨wc, wcmem, rvwc⟩
      use wc
      simp_all only [true_and]
      use wb
  · use b

/-- info: 'Test.bisim_trans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms bisim_trans
/-- info: 'Test.bisim_symm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bisim_symm
/-- info: 'Test.bisim_refl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms bisim_refl

end Test


namespace WeakBisimTest

/-- An FSM without input, but with silent/tau steps -/
structure FSM where
  S : Type
  d : S → S
  /-- if `o s = none`, it's a silent step -/
  o : S → Option Bool

coinductive WeakBisim (fsm : FSM) : fsm.S → fsm.S → Prop :=
  | step {s t : fsm.S} :
    (fsm.o s = fsm.o t)
    → WeakBisim (fsm.d s) (fsm.d t)
    → WeakBisim s t
  | tauLeft {s t : fsm.S} :
    fsm.o s = none → WeakBisim (fsm.d s) t → WeakBisim s t
  | tauRight {s t : fsm.S} :
    fsm.o t = none → WeakBisim s (fsm.d t) → WeakBisim s t

/--
info: def WeakBisimTest.WeakBisim : (fsm : FSM) → fsm.S → fsm.S → Prop :=
fun fsm x x_1 => ∃ R, WeakBisim.Is fsm R ∧ R x x_1
-/
#guard_msgs in #print WeakBisim

/--
info: @[reducible] def WeakBisimTest.WeakBisim.Is : (fsm : FSM) → (fsm.S → fsm.S → Prop) → Prop :=
fun fsm WeakBisim =>
  (∀ {s t : fsm.S}, WeakBisim s t → (
    fsm.o t = none ∧ WeakBisim s (fsm.d t) ∨
    fsm.o s = fsm.o t ∧ WeakBisim (fsm.d s) (fsm.d t)) ∨
    fsm.o s = none ∧ WeakBisim (fsm.d s) t))
-/
#guard_msgs in #print WeakBisim.Is
