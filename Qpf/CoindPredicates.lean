import Std.Tactic.OpenPrivate
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
  d : S → Nat → S
  A : S → Prop

coinductive Bisim (fsm : FSM) : fsm.S → fsm.S → Prop :=
  | step {s t : fsm.S} :
    (fsm.A s ↔ fsm.A t)
    → (∀ c, Bisim (fsm.d s c) (fsm.d t c))
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
  exists fun a b => rel b a
  simp_all
  intro a₁ b₁ holds
  specialize relIsBisim holds
  simp_all only [implies_true, and_self]

theorem Bisim.unfold {f} : Bisim.Is f (Bisim f) := by
  rintro s t ⟨R, h_is, h_Rst⟩
  constructor
  · exact (h_is h_Rst).1
  · intro c; exact ⟨R, h_is, (h_is h_Rst).2 c⟩

-- case principle!
@[elab_as_elim]
def Bisim.casesOn {f : FSM} {s t}
    {motive : Bisim f s t → Prop}
    (h : Bisim f s t)
    (step : ∀ {s t}, (f.A s ↔ f.A t)
      → (∀ c, Bisim f (f.d s c) (f.d t c)) → motive h) :
    motive h := by
  have ⟨R, h_is, h_R⟩ := h
  have ⟨h₁, h₂⟩ := h_is h_R
  apply step h₁ (fun c => ⟨R, h_is, h₂ c⟩)

theorem bisim_trans (h_ab : Bisim f a b) (h_bc : Bisim f b c) :
    Bisim f a c := by
  coinduction
    using (fun s t => ∃ u, Bisim f s u ∧ Bisim f u t)
    with s t h_Rst
  · rcases h_Rst with ⟨u, h_su, h_ut⟩
    have ⟨h_su₁, h_su₂⟩ := h_su.unfold
    have ⟨h_ut₁, h_ut₂⟩ := h_ut.unfold
    refine ⟨?_, ?_⟩
    · rw [h_su₁, h_ut₁]
    · intro c; exact ⟨_, h_su₂ c, h_ut₂ c⟩
  · exact ⟨b, h_ab, h_bc⟩

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


coinductive Const (b? : Option Bool) (fsm : FSM) : fsm.S → Prop
  | step {s} :
      fsm.o s = b? → Const (fsm.d s) → Const s

/--
info: @[reducible] def WeakBisimTest.Const.Is : Option Bool → (fsm : FSM) → (fsm.S → Prop) → Prop :=
fun b? fsm Const => ∀ {s : fsm.S}, Const s → fsm.o s = b? ∧ Const (fsm.d s)
-/
#guard_msgs in #print Const.Is


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

end WeakBisimTest
