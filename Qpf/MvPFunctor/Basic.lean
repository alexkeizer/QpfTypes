/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Multivariate polynomial functors.

Note: eventually the W and M constructions as multivariate polynomial functors will go here.
-/
import Qpf.MvFunctor
import Qpf.PFunctor
universe u v

/-- An  `n`-variate polynomial functor is defined by
    * a set A, and
    * a family of n-tuples of sets (Ba)_{a ∈ A}, i.e., where each Ba = (Ba1, Ba2, ..., Ban)
      consists on `n` sets
-/
structure MvPFunctor (n : Nat) :=
(A : Type u) (B : A → TypeVec.{u} n)

namespace MvPFunctor
open MvFunctor (liftp liftr)

variable {n m : Nat} (P : MvPFunctor.{u} n)

/-- Let `X = (X1, ..., Xn)` be an n-tuple of sets, then an element of `P(X1, ..., Xn)` consists of
    * a 'shape' `a ∈ A`, and
    * an arrow `g: Ba ⟹ X`, which is an n-tuple of functions `(Ba)_i → Xi`
-/
def obj (α : TypeVec.{u} n) : Type u 
  := Σ a : P.A, P.B a ⟹ α

/-- Let `f : X ⟹ Y` be an arrow of `TypeVec`s, then `P(f) : P(X) ⟹ Y` is defined by 
    pre-composition of `f` with the arrow `g` in `P(X)`
-/
def map {α β : TypeVec n} (f : α ⟹ β) : P.obj α → P.obj β :=
λ ⟨a, g⟩ => ⟨a, TypeVec.comp f g⟩

/-- An MvPFunctor is a special case of MvFunctor -/
instance : MvFunctor P.obj :=
⟨@MvPFunctor.map n P⟩

theorem map_eq {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f : P.B a ⟹ α) :
  @MvFunctor.map _ P.obj _ _ _ g ⟨a, f⟩ = ⟨a, g ⊚ f⟩ :=
rfl

theorem id_map {α : TypeVec n} : ∀ x : P.obj α, TypeVec.id <$$> x = x
| ⟨a, g⟩ => rfl

theorem comp_map {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ) :
  ∀ x : P.obj α, (g ⊚ f) <$$> x = g <$$> (f <$$> x)
| ⟨a, h⟩ => rfl

/-- To wit, MvPFunctors are always Lawful -/
instance : MvFunctor.Lawful P.obj := 
⟨@id_map n P, @comp_map n P⟩

#check @Sigma

/-- Composition of multivariate polynomial functors 
  
  Suppose that `F(X₁, ..., X_n)  = Σ (a : A)    , ∀ i < n, (B(a))_i   → X_i` and
               `F_j(X₁, ... X_m) = Σ (a_j : A_j), ∀ i < m, (B_j(a))_i → X_i`
  For some `X₁, ..., X_m`, let `(a_j, f_j0, ..., f_jm) = F(X₁, ..., X_m)`
  Then their naive composition
  `F(F₁(X₁, ... Xm), F₂(X₁, ... Xm), ..., Fn(X₁, ... Xm))`
  is
  ` `
-/
def comp (P : MvPFunctor.{u} n) (Q : fin' n → MvPFunctor.{u} m) : MvPFunctor m :=
{ A := Σ a₂ : P.A, ∀ i, P.B a₂ i → (Q i).A, 
  B := λ a i => Σ (j : fin' n), Σ (b : P.B a.1 j), (Q j).2 (a.snd j b) i
}

variable {P} {Q : fin' n → MvPFunctor.{u} m} {α β : TypeVec.{u} m}

def comp.mk (x : P.obj (λ i => (Q i).obj α)) : (comp P Q).obj α :=
⟨ ⟨ x.1, λ i a => (x.2 _ a).1  ⟩, 
  λ i a => (x.snd a.fst (a.snd).fst).snd i (a.snd).snd 
⟩


/- FIXME: 

section
  #print apply
  variable (x: (comp P Q).apply α) (i : fin' n) (a : B P x.fst.fst i)
  #check (Sigma.snd x.fst i a)
  #check B
  #check B (Q i) (Sigma.snd x.fst i a) ⟹ α
end

def comp.get (x : (comp P Q).apply α) : P.obj (λ i => (Q i).apply α) :=
Sigma.mk x.1.1 (λ i a => ⟨x.fst.snd i a, (λ (i : fin' n) (j : fin' m) => (_ : α j)
  -- ⟨λ (j : fin' m) (b : (Q i).B _ j) => _⟩
  -- ⟨λ  => x.snd j ⟨i, ⟨a, b⟩⟩⟩
) i⟩ )
-- ⟨ x.1.1, λ i a => ⟨x.fst.snd i a, ⟨λ (j : fin' m) (b : (Q i).B _ j) => x.snd j ⟨i, ⟨a, b⟩⟩⟩⟩⟩


theorem comp.get_map (f : α ⟹ β) (x : (comp P Q).apply α) :
  comp.get (f <$$> x) = (λ i (x : (Q i).apply α) => f <$$> x) <$$> comp.get x :=
by cases x; rfl

@[simp]
theorem comp.get_mk (x : P.obj (λ i => (Q i).apply α)) : comp.get (comp.mk x) = x :=
begin
  cases x,
  simp! [comp.get,comp.mk],
  ext; intros; refl
end

@[simp]
theorem comp.mk_get (x : (comp P Q).apply α) : comp.mk (comp.get x) = x :=
begin
  cases x,
  dsimp [comp.get,comp.mk],
  ext; intros, refl, refl,
  congr, ext; intros; refl,
  ext, congr, rcases x_1 with ⟨a,b,c⟩; refl,
end

-/

/-
lifting predicates and relations
-/

theorem liftp_iff {α : TypeVec n} (p : ∀ ⦃i⦄ , α i → Prop) (x : P.obj α) :
  liftp p x ↔ ∃ a f, x = ⟨a, f⟩ ∧ ∀ i j, p (f i j) :=
by
  apply Iff.intro
  {
    intro ⟨⟨a, f⟩, hy⟩;
    refine ⟨a, λ i j => (f i j).val, (Eq.symm hy), λ i j => (f i j).property⟩
  }
  {
    intro ⟨a, f, ⟨xeq, pf⟩⟩;
    let f' := (λ (i : fin' n) (b : _) => Subtype.mk (f i b) (pf i b));
    apply Exists.intro ⟨a, λ i j => ⟨f i j, pf i j⟩⟩;
    rw [xeq]
    rfl
  }

theorem liftr_iff {α : TypeVec n} (r : ∀ {i}, α i → α i → Prop) (x y : P.obj α) :
  liftr r x y ↔ ∃ a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ ∀ i j, r (f₀ i j) (f₁ i j) :=
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
split_fun f' f

end MvPFunctor