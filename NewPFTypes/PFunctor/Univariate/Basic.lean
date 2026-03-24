/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/

/-!
# Polynomial Functors

This file defines polynomial functors and the W-type construction as a polynomial functor.
-/

universe u v uA uB uA₁ uB₁ uA₂ uB₂ v₁ v₂ v₃

/-- A polynomial functor `P` is given by a type `A` and a family `B` of types over `A`. `P` maps
any type `α` to a new type `P α`, which is defined as the sigma type `Σ x, P.B x → α`.

An element of `P α` is a pair `⟨a, f⟩`, where `a` is an element of a type `A` and
`f : B a → α`. Think of `a` as the shape of the object and `f` as an index to the relevant
elements of `α`.
-/
structure PFunctor where
  /-- The head type -/
  A : Type uA
  /-- The child family of types -/
  B : A → Type uB

namespace PFunctor

instance : Inhabited PFunctor :=
  ⟨⟨default, default⟩⟩

variable (P : PFunctor.{uA, uB}) {α : Type v₁} {β : Type v₂} {γ : Type v₃}

/-- Applying `P` to an object of `Type` -/
@[coe]
def Obj (α : Type v) : Type (max v uA uB) :=
  Σ x : P.A, P.B x → α

instance : CoeFun PFunctor.{uA, uB} (fun _ => Type v → Type (max v uA uB)) where
  coe := Obj

/-- Applying `P` to a morphism of `Type` -/
def map (f : α → β) : P α → P β :=
  fun ⟨a, g⟩ => ⟨a, f ∘ g⟩

instance Obj.inhabited [Inhabited P.A] [Inhabited α] : Inhabited (P α) :=
  ⟨⟨default, default⟩⟩

instance : Functor P.Obj where map := @map P

/-- We prefer `PFunctor.map` to `Functor.map` because it is universe-polymorphic. -/
@[simp]
theorem map_eq_map {α β : Type v} (f : α → β) (x : P α) : f <$> x = P.map f x :=
  rfl

@[simp]
protected theorem map_eq (f : α → β) (a : P.A) (g : P.B a → α) :
    P.map f ⟨a, g⟩ = ⟨a, f ∘ g⟩ :=
  rfl

@[simp]
protected theorem id_map : ∀ x : P α, P.map id x = x := fun ⟨_, _⟩ => rfl

@[simp]
protected theorem map_map (f : α → β) (g : β → γ) :
    ∀ x : P α, P.map g (P.map f x) = P.map (g ∘ f) x := fun ⟨_, _⟩ => rfl

instance : LawfulFunctor (Obj.{v} P) where
  map_const := rfl
  id_map x := P.id_map x
  comp_map f g x := P.map_map f g x |>.symm

/-- The W-type (well-founded tree) associated to a polynomial functor.
    Nodes are labeled by shapes `a : P.A` and branching is given by `P.B a`. -/
inductive W (P : PFunctor.{uA, uB}) : Type (max uA uB)
  | mk (a : P.A) (f : P.B a → W P) : W P

/- Inhabitants of W types is awkward to encode as an instance assumption because there needs to be a
value `a : P.A` such that `P.B a` is empty to yield a finite tree. -/

variable {P}

/-- The root element of a W tree -/
def W.head : W P → P.A
  | .mk a _f => a

/-- The children of the root of a W tree -/
def W.children : ∀ x : W P, P.B (W.head x) → W P
  | .mk _a f => f

/-- The destructor for W-types -/
def W.dest : W P → P (W P)
  | .mk a f => ⟨a, f⟩

/-- The constructor for W-types -/
def W.mk' : P (W P) → W P
  | ⟨a, f⟩ => .mk a f

@[simp]
theorem W.dest_mk' (p : P (W P)) : W.dest (W.mk' p) = p := by cases p; rfl

@[simp]
theorem W.mk'_dest (p : W P) : W.mk' (W.dest p) = p := by cases p; rfl

variable (P)

/-- `Idx` identifies a location inside the application of a polynomial functor. For `F : PFunctor`,
`x : F α` and `i : F.Idx`, `i` can designate one part of `x` or is invalid, if `i.1 ≠ x.1`. -/
def Idx : Type (max uA uB) :=
  Σ x : P.A, P.B x

instance Idx.inhabited [Inhabited P.A] [Inhabited (P.B default)] : Inhabited P.Idx :=
  ⟨⟨default, default⟩⟩

variable {P}

/-- `x.iget i` takes the component of `x` designated by `i` if any, or returns a default value -/
def Obj.iget [DecidableEq P.A] {α} [Inhabited α] (x : P α) (i : P.Idx) : α :=
  if h : i.1 = x.1 then x.2 (cast (congrArg _ h) i.2) else default

@[simp]
theorem fst_map (x : P α) (f : α → β) : (P.map f x).1 = x.1 := by cases x; rfl

@[simp]
theorem iget_map [DecidableEq P.A] [Inhabited α] [Inhabited β] (x : P α)
    (f : α → β) (i : P.Idx) (h : i.1 = x.1) : (P.map f x).iget i = f (x.iget i) := by
  simp only [Obj.iget, fst_map, *, dif_pos]
  cases x
  rfl

end PFunctor

/-
Composition of polynomial functors.
-/
namespace PFunctor

/-- Composition for polynomial functors -/
def comp (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) :
    PFunctor.{max uA₁ uA₂ uB₂, max uB₁ uB₂} :=
  ⟨Σ a₂ : P₂.1, P₂.2 a₂ → P₁.1, fun a₂a₁ => Σ u : P₂.2 a₂a₁.1, P₁.2 (a₂a₁.2 u)⟩

/-- Constructor for composition -/
def comp.mk (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) {α : Type v}
    (x : P₂ (P₁ α)) : comp P₂ P₁ α :=
  ⟨⟨x.1, Sigma.fst ∘ x.2⟩, fun a₂a₁ => (x.2 a₂a₁.1).2 a₂a₁.2⟩

/-- Destructor for composition -/
def comp.get (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) {α : Type v}
    (x : comp P₂ P₁ α) : P₂ (P₁ α) :=
  ⟨x.1.1, fun a₂ => ⟨x.1.2 a₂, fun a₁ => x.2 ⟨a₂, a₁⟩⟩⟩

end PFunctor

/-
Lifting predicates and relations.
-/
namespace PFunctor

variable {P : PFunctor.{uA, uB}}

/-- `Liftp p x` asserts that every element in `x` satisfies `p`. -/
def Liftp {α : Type u} (p : α → Prop) (x : P α) : Prop :=
  ∃ u : P { a // p a }, P.map Subtype.val u = x

/-- `Liftr r x y` asserts that every pair of corresponding elements in `x` and `y` is related
by `r`. -/
def Liftr {α : Type u} (r : α → α → Prop) (x y : P α) : Prop :=
  ∃ u : P { p : α × α // r p.1 p.2 },
    P.map (Prod.fst ∘ Subtype.val) u = x ∧ P.map (Prod.snd ∘ Subtype.val) u = y

/-- `supp x` is the set of elements that appear in `x`, as a predicate on `α`. -/
def supp {α : Type u} (x : P α) : α → Prop :=
  fun a => ∀ p, Liftp p x → p a

theorem liftp_iff {α : Type u} (p : α → Prop) (x : P α) :
    Liftp p x ↔ ∃ a f, x = ⟨a, f⟩ ∧ ∀ i, p (f i) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : y with ⟨a, f⟩
    refine ⟨a, fun i => (f i).val, ?_, fun i => (f i).property⟩
    rw [← hy, h]; rfl
  rintro ⟨a, f, xeq, pf⟩
  exact ⟨⟨a, fun i => ⟨f i, pf i⟩⟩, by rw [xeq]; rfl⟩

theorem liftp_iff' {α : Type u} (p : α → Prop) (a : P.A) (f : P.B a → α) :
    Liftp p (⟨a, f⟩ : P α) ↔ ∀ i, p (f i) := by
  simp only [liftp_iff]
  constructor
  · rintro ⟨a', f', heq, h'⟩
    cases heq; exact h'
  intro h
  exact ⟨a, f, rfl, h⟩

theorem liftr_iff {α : Type u} (r : α → α → Prop) (x y : P α) :
    Liftr r x y ↔ ∃ a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ ∀ i, r (f₀ i) (f₁ i) := by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : u with ⟨a, f⟩
    exact ⟨a, fun i => (f i).val.fst, fun i => (f i).val.snd,
      by rw [← xeq, h]; rfl,
      by rw [← yeq, h]; rfl,
      fun i => (f i).property⟩
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  exact ⟨⟨a, fun i => ⟨(f₀ i, f₁ i), h i⟩⟩,
    by rw [xeq]; rfl,
    by rw [yeq]; rfl⟩

/-- The support of `⟨a, f⟩` is exactly the range of `f`. -/
theorem supp_eq {α : Type u} (a : P.A) (f : P.B a → α) :
    supp (⟨a, f⟩ : P α) = fun x => ∃ i, f i = x := by
  funext x
  apply propext
  simp only [supp]
  constructor
  · intro h
    apply h (fun x => ∃ i, f i = x)
    rw [liftp_iff']
    intro i; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    intro p hp
    rw [liftp_iff'] at hp
    exact hp i

end PFunctor
