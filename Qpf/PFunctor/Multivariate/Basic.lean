/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Multivariate polynomial functors.

Note: eventually the W and M constructions as multivariate polynomial functors will go here.
-/
import Qpf.MvFunctor
import Qpf.PFunctor.Univariate.Basic
import Qpf.Mathlib
import Qpf.Util.HEq

universe u v

/-- An  `n`-variate polynomial functor is defined by
    * a set A, and
    * a family of n-tuples of sets (Ba)_{a ∈ A}, i.e., where each Ba = (Ba1, Ba2, ..., Ban)
      consists on `n` sets
-/
structure MvPFunctor (n : Nat) :=
(A : Type u) (B : A → TypeVec.{u} n)

namespace MvPFunctor
open MvFunctor (Liftp Liftr)

variable {n m : Nat} (P : MvPFunctor.{u} n)

/-- Let `X = (X1, ..., Xn)` be an n-tuple of sets, then an element of `P(X1, ..., Xn)` consists of
    * a 'shape' `a ∈ A`, and
    * an arrow `g: Ba ⟹ X`, which is an n-tuple of functions `(Ba)_i → Xi`
-/
def Obj (α : TypeVec.{u} n) : Type u 
  := Σ a : P.A, P.B a ⟹ α

/-- Let `f : X ⟹ Y` be an arrow of `TypeVec`s, then `P(f) : P(X) ⟹ Y` is defined by 
    pre-composition of `f` with the arrow `g` in `P(X)`
-/
def map {α β : TypeVec n} (f : α ⟹ β) : P.Obj α → P.Obj β :=
λ ⟨a, g⟩ => ⟨a, TypeVec.comp f g⟩

instance : Inhabited (MvPFunctor n) :=
  ⟨⟨default, fun _ => default⟩⟩

instance Obj.inhabited {α : TypeVec n} [Inhabited P.A] [∀ i, Inhabited (α i)] : Inhabited (P.Obj α) :=
  ⟨⟨default, fun _ _ => default⟩⟩

/-- An MvPFunctor is a special case of MvFunctor -/
instance : MvFunctor P.Obj :=
⟨@MvPFunctor.map n P⟩

theorem map_eq {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f : P.B a ⟹ α) :
  @MvFunctor.map _ P.Obj _ _ _ g ⟨a, f⟩ = ⟨a, g ⊚ f⟩ :=
rfl

theorem id_map {α : TypeVec n} : ∀ x : P.Obj α, TypeVec.id <$$> x = x
| ⟨a, g⟩ => rfl

theorem comp_map {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ) :
  ∀ x : P.Obj α, (g ⊚ f) <$$> x = g <$$> (f <$$> x)
| ⟨a, h⟩ => rfl

/-- To wit, MvPFunctors are always Lawful -/
instance : LawfulMvFunctor P.Obj := 
⟨@id_map n P, @comp_map n P⟩


/-- Constant functor where the input object does not affect the output -/
def Const (n : Nat) (A : Type u) : MvPFunctor n :=
  { A, B := fun a i => PEmpty }

section Const

variable (n : Nat) {A : Type u} {α β : TypeVec.{u} n}

/-- Constructor for the constant functor -/
def Const.mk (x : A) {α} : (Const n A).Obj α :=
  ⟨x, fun i a => PEmpty.elim a⟩

-- When rebinding n, we have to also rebind α and β, since their type depends on n
variable {n: Nat} {A : Type u} {α β : TypeVec.{u} n}

/-- Destructor for the constant functor -/
def Const.get (x : (Const n A).Obj α) : A :=
  x.1

@[simp]
theorem Const.get_map (f : α ⟹ β) (x : (Const n A).Obj α) : Const.get (f <$$> x) = Const.get x := by
  cases x
  rfl

@[simp]
theorem Const.get_mk (x : A) : Const.get (Const.mk n x : (Const n A).Obj α) = x := by
  rfl

@[simp]
theorem Const.mk_get (x : (Const n A).Obj α) : Const.mk n (Const.get x) = x := by
  cases x
  simp [Const.get, Const.mk]
  apply congrArg
  funext i a;
  trivial

end Const

/-- Functor composition on multivariate polynomial functors
  
  Suppose that `F(X₁, ..., X_n)  = Σ (a : A)    , ∀ i < n, (B(a))_i   → X_i` and
               `F_j(X₁, ... X_m) = Σ (a_j : A_j), ∀ i < m, (B_j(a))_i → X_i`
  For some `X₁, ..., X_m`, let `(a_j, f_j0, ..., f_jm) = F(X₁, ..., X_m)`
  Then their naive composition
  `F(F₁(X₁, ... Xm), F₂(X₁, ... Xm), ..., Fn(X₁, ... Xm))`
  is
  ` `
-/
def Comp (P : MvPFunctor.{u} n) (Q : Fin2 n → MvPFunctor.{u} m) : MvPFunctor m :=
{ A := Σ a₂ : P.A, ∀ i, P.B a₂ i → (Q i).A, 
  B := λ a i => Σ (j : Fin2 n), Σ (b : P.B a.1 j), (Q j).2 (a.snd j b) i
}

variable {P} {Q : Fin2 n → MvPFunctor.{u} m} {α β : TypeVec.{u} m}

namespace Comp

/-- Constructor for functor composition -/
def mk (x : P.Obj (λ i => (Q i).Obj α)) : (Comp P Q).Obj α :=
⟨ ⟨ x.1, λ i a => (x.2 _ a).1  ⟩, 
  λ i a => (x.snd a.fst (a.snd).fst).snd i (a.snd).snd 
⟩

/-- Destructor for functor composition -/
def get (x : (Comp P Q).Obj α) : P.Obj fun i => (Q i).Obj α :=
  ⟨x.1.1, fun i a => ⟨x.fst.snd i a, fun j (b : (Q i).B _ j) => x.snd j ⟨i, ⟨a, b⟩⟩⟩⟩

theorem get_map (f : α ⟹ β) (x : (Comp P Q).Obj α) :
  Comp.get (f <$$> x) = (fun i (x : (Q i).Obj α) => f <$$> x) <$$> Comp.get x := 
by
  cases x
  rfl

@[simp]
theorem get_mk (x : P.Obj fun i => (Q i).Obj α) : Comp.get (Comp.mk x) = x := 
by
  cases x
  simp [Comp.get, Comp.mk]
  apply congrArg
  rfl  

@[simp]
theorem mk_get (x : (Comp P Q).Obj α) : Comp.mk (Comp.get x) = x := by
  cases x
  simp [Comp.get, Comp.mk]
  rfl

end Comp
  

/-
lifting predicates and relations
-/

theorem liftp_iff {α : TypeVec n} (p : ∀ ⦃i⦄ , α i → Prop) (x : P.Obj α) :
  Liftp p x ↔ ∃ a f, x = ⟨a, f⟩ ∧ ∀ i j, p (f i j) :=
by
  apply Iff.intro
  {
    intro ⟨⟨a, f⟩, hy⟩;
    refine ⟨a, λ i j => (f i j).val, (Eq.symm hy), λ i j => (f i j).property⟩
  }
  {
    intro ⟨a, f, ⟨xeq, pf⟩⟩;
    let f' := (λ (i : Fin2 n) (b : _) => Subtype.mk (f i b) (pf i b));
    apply Exists.intro ⟨a, λ i j => ⟨f i j, pf i j⟩⟩;
    rw [xeq]
    rfl
  }

theorem liftp_iff' {α : TypeVec n} (p : ∀ ⦃i⦄, α i → Prop) (a : P.A) (f : P.B a ⟹ α) :
    @Liftp.{u} _ P.Obj _ α p ⟨a, f⟩ ↔ ∀ i x, p (f i x) := 
by
  simp [liftp_iff] <;> constructor
  · rintro ⟨a, f, h₁, h₂⟩
    cases h₁
    assumption
  
  . intro
    repeat'
      first |
        constructor|
        assumption

theorem liftr_iff {α : TypeVec n} (r : ∀ {i}, α i → α i → Prop) (x y : P.Obj α) :
  Liftr r x y ↔ ∃ a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ ∀ i j, r (f₀ i j) (f₁ i j) :=
by 
  apply Iff.intro
  {
    intro ⟨⟨a, f⟩, xeq, yeq⟩;
    apply Exists.intro a;
    apply Exists.intro λ i j => (f i j).val.fst;
    apply Exists.intro λ i j => (f i j).val.snd;
    apply And.intro; 
      { rw [←xeq]; rfl }
    apply And.intro; 
      { rw [←yeq]; rfl }
    intro i j;
    exact (f i j).property
  }
  {
    intro ⟨a, f₀, f₁, ⟨xeq, yeq, h⟩⟩;
    apply Exists.intro ⟨a, λ i j => ⟨(f₀ i j, f₁ i j), h i j⟩⟩;
    apply And.intro;
      {rw [xeq]; rfl}
      {rw [yeq]; rfl}
  }

  -- open Set MvFunctor

  theorem supp_eq {α : TypeVec n} (a : P.A) (f : P.B a ⟹ α) i :
    @MvFunctor.supp.{u} _ P.Obj _ α (⟨a, f⟩ : P.Obj α) i = Set.image (f i) Set.univ := by
  ext x
  simp only [MvFunctor.supp, Set.image_univ, Set.mem_range, Set.mem_set_of_eq]
  constructor <;> intro h
  · apply @h fun i x => ∃ y : P.B a i, f i y = x
    rw [liftp_iff']
    intros
    refine' ⟨_, rfl⟩
    
  · simp only [liftp_iff']
    rcases h with ⟨y, h⟩
    subst x
    simp [setOf]
    intros p h
    apply h

end MvPFunctor

/-
Decomposing an n+1-ary pfunctor.
-/

namespace MvPFunctor
open TypeVec
variable {n : Nat} (P : MvPFunctor.{u} (n+1))

def drop : MvPFunctor n :=
{ A := P.A, B := λ a => (P.B a).drop }

def last : PFunctor :=
{ A := P.A, B := λ a => (P.B a).last }

@[reducible] def append_contents {α : TypeVec n} {β : Type _}
    {a : P.A} (f' : P.drop.B a ⟹ α) (f : P.last.B a → β) :
  P.B a ⟹ α.append1 β :=
splitFun f' f

end MvPFunctor

