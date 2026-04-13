/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
module

public import QPFTypes.TypeVec
public import QPFTypes.MvFunctor
public import QPFTypes.PFunctor.Univariate.Basic

/-!
# Multivariate polynomial functors

Multivariate polynomial functors map a type vector `α` to the type `Σ a : A, B a ⟹ α`,
with `A : Type` and `B : A → TypeVec n`. They interact well with Lean's inductive
definitions because they guarantee that occurrences of `α` are positive.
-/
@[expose] public section

namespace QPFTypes
open TypeVec

universe u

/-- Multivariate polynomial functors -/
structure MvPFunctor (n : Nat) where
  /-- The head type -/
  A : Type u
  /-- The child family of type vectors -/
  B : A → TypeVec.{u} n

namespace MvPFunctor

variable {n m : Nat} (P : MvPFunctor.{u} n)

/-- Applying `P` to an object of `TypeVec` -/
@[coe]
def Obj (α : TypeVec.{u} n) : Type u :=
  Σ a : P.A, P.B a ⟹ α
instance : CoeFun (MvPFunctor.{u} n) (fun _ => TypeVec.{u} n → Type u) where
  coe := Obj

/-! ### Inhabitedness -/

instance : Inhabited (MvPFunctor n) :=
  ⟨⟨default, default⟩⟩

instance Obj.inhabited {α : TypeVec n} [Inhabited P.A] [∀ i, Inhabited (α i)] :
    Inhabited (P α) :=
  ⟨⟨default, fun _ _ => default⟩⟩

/-! ### Mapping Functions -/

/-- Applying `P` to a morphism of `TypeVec` -/
instance : MvFunctor P where
  map f := fun ⟨a, g⟩ => ⟨a, f ⊚ g⟩
@[grind] abbrev map (f : α ⟹ β) (x : P α) := f <$$> x

section MapLemmas

@[simp, grind =]
theorem map_eq {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f : P.B a ⟹ α) :
    P.map g ⟨a, f⟩ = ⟨a, g ⊚ f⟩ :=
  rfl

@[simp, grind =]
theorem id_map {α : TypeVec n} : ∀ x : P α, P.map TypeVec.id x = x
  | ⟨_, _⟩ => rfl

@[simp, grind =]
theorem comp_map {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ) :
    ∀ x : P α, P.map (g ⊚ f) x = P.map g (P.map f x)
  | ⟨_, _⟩ => rfl

instance : LawfulMvFunctor P where
  id_map := by simp
  comp_map := by simp

end MapLemmas

/-
Constant functor.
-/

/-- Constant functor where the input object does not affect the output -/
def const (n : Nat) (A : Type u) : MvPFunctor n :=
  { A, B := fun _ _ => PEmpty }

section Const

variable (n) {A : Type u} {α β : TypeVec.{u} n}

/-- Constructor for the constant functor -/
def const.mk (x : A) {α} : const n A α :=
  ⟨x, fun _ a => PEmpty.elim a⟩

variable {n}

/-- Destructor for the constant functor -/
def const.get (x : const n A α) : A :=
  x.1

@[simp]
theorem const.get_map (f : α ⟹ β) (x : const n A α) :
    const.get ((const n A).map f x) = const.get x := by
  cases x; rfl

@[simp]
theorem const.get_mk (x : A) : const.get (const.mk n x : const n A α) = x := rfl

@[simp]
theorem const.mk_get (x : const n A α) : const.mk n (const.get x) = x := by
  cases x
  simp only [const.get, const.mk]
  congr 1
  funext _ a
  exact PEmpty.elim a

end Const

/-
Functor composition.
-/

/-- Functor composition on polynomial functors -/
def comp (P : MvPFunctor.{u} n) (Q : Fin n → MvPFunctor.{u} m) : MvPFunctor m where
  A := Σ a : P.A, ∀ i, P.B a i → (Q i).A
  B a i := Σ (j : Fin n) (b : P.B a.1 j), (Q j).B (a.2 j b) i

variable {P} {Q : Fin n → MvPFunctor.{u} m} {α β : TypeVec.{u} m}

/-- Constructor for functor composition -/
def comp.mk (x : P (fun i => Q i α)) : comp P Q α :=
  ⟨⟨x.1, fun i a => (x.2 i a).1⟩, fun i a => (x.2 a.1 a.2.1).2 i a.2.2⟩

/-- Destructor for functor composition -/
def comp.get (x : comp P Q α) : P (fun i => Q i α) :=
  ⟨x.1.1, fun i a => ⟨x.1.2 i a, fun j b => x.2 j ⟨i, ⟨a, b⟩⟩⟩⟩

theorem comp.get_map (f : α ⟹ β) (x : comp P Q α) :
    comp.get ((comp P Q).map f x) =
    P.map (fun i (y : Q i α) => (Q i).map f y) (comp.get x) := by
  rfl

@[simp]
theorem comp.get_mk (x : P (fun i => Q i α)) : comp.get (comp.mk x) = x := by
  rfl

@[simp]
theorem comp.mk_get (x : comp P Q α) : comp.mk (comp.get x) = x := by
  rfl

/-
Lifting predicates and relations.
-/

variable (P : MvPFunctor.{u} n)

/-- `LiftP p x` asserts that every element in `x` satisfies `p`. -/
def LiftP {α : TypeVec n} (p : ∀ i, α i → Prop) (x : P α) : Prop :=
  ∃ u : P (fun i => { a // p i a }), P.map (fun _ => Subtype.val) u = x

/-- `LiftR r x y` asserts that every pair of corresponding elements in `x` and `y` is related
by `r`. -/
def LiftR {α : TypeVec n} (r : ∀ ⦃i⦄, α i → α i → Prop) (x y : P α) : Prop :=
  ∃ u : P (fun i => { p : α i × α i // r p.1 p.2 }),
    P.map (fun _ t => t.val.1) u = x ∧ P.map (fun _ t => t.val.2) u = y

/-- `supp x i` is the set of `α i` values that appear in `x`, as a predicate. -/
def supp {α : TypeVec n} (x : P α) (i : Fin n) : α i → Prop :=
  fun y => ∀ ⦃p : ∀ i, α i → Prop⦄, LiftP P p x → p i y

variable {P}

theorem liftP_iff {α : TypeVec n} (p : ∀ ⦃i⦄, α i → Prop) (x : P α) :
    LiftP P p x ↔ ∃ a f, x = ⟨a, f⟩ ∧ ∀ i j, p (f i j) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : y with ⟨a, f⟩
    refine ⟨a, fun i j => (f i j).val, ?_, fun i j => (f i j).property⟩
    rw [← hy, h, map_eq]; rfl
  rintro ⟨a, f, xeq, pf⟩
  exact ⟨⟨a, fun i j => ⟨f i j, pf i j⟩⟩, by rw [xeq]; rfl⟩

theorem liftP_iff' {α : TypeVec n} (p : ∀ ⦃i⦄, α i → Prop) (a : P.A) (f : P.B a ⟹ α) :
    LiftP P p ⟨a, f⟩ ↔ ∀ i j, p (f i j) := by
  simp only [liftP_iff]
  constructor
  · rintro ⟨_, _, ⟨⟩, h⟩; exact h
  · intro h; exact ⟨a, f, rfl, h⟩

theorem liftR_iff {α : TypeVec n} (r : ∀ ⦃i⦄, α i → α i → Prop) (x y : P α) :
    LiftR P r x y ↔ ∃ a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ ∀ i j, r (f₀ i j) (f₁ i j) := by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : u with ⟨a, f⟩
    exact ⟨a, fun i j => (f i j).val.1, fun i j => (f i j).val.2,
      by rw [← xeq, h, map_eq]; rfl,
      by rw [← yeq, h, map_eq]; rfl,
      fun i j => (f i j).property⟩
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  exact ⟨⟨a, fun i j => ⟨(f₀ i j, f₁ i j), h i j⟩⟩,
    by rw [xeq, map_eq]; rfl,
    by rw [yeq, map_eq]; rfl⟩

theorem supp_eq {α : TypeVec n} (a : P.A) (f : P.B a ⟹ α) (i) :
    supp P ⟨a, f⟩ i = fun x => ∃ j, f i j = x := by
  funext x
  apply propext
  simp only [supp]
  constructor
  · intro h
    apply h (p := fun i x => ∃ j, f i j = x)
    rw [liftP_iff']
    intro i j; exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    intro p hp
    rw [liftP_iff'] at hp
    exact hp i j

/-
Decomposing an (n+1)-ary polynomial functor.
-/

variable (P : MvPFunctor.{u} (n + 1))

/-- Split polynomial functor, get an n-ary functor from an `(n+1)`-ary functor -/
def drop : MvPFunctor n where
  A := P.A
  B a := (P.B a).drop

/-- Split polynomial functor, get a univariate functor from an `(n+1)`-ary functor -/
def last : PFunctor where
  A := P.A
  B a := (P.B a).last

/-- Append arrows of a polynomial functor application -/
abbrev appendContents {α : TypeVec n} {β : Type _} {a : P.A}
    (f' : P.drop.B a ⟹ α) (f : P.last.B a → β) : P.B a ⟹ (α ::: β) :=
  splitFun f' f

end MvPFunctor
