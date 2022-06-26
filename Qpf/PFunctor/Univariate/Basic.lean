/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/

import Qpf.Mathlib
import Qpf.MathlibPort.Functor
import Qpf.MathlibPort.Set

/-!
# Polynomial functors
This file defines polynomial functors and the W-type construction as a
polynomial functor.  (For the M-type construction, see
pfunctor/M.lean.)
-/

universe u

/--
A polynomial functor `P` is given by a type `A` and a family `B` of types over `A`. `P` maps
any type `α` to a new type `P.Obj α`, which is defined as the sigma type `Σ x, P.B x → α`.
An element of `P.Obj α` is a pair `⟨a, f⟩`, where `a` is an element of a type `A` and
`f : B a → α`. Think of `a` as the shape of the object and `f` as an index to the relevant
elements of `α`.
-/

structure PFunctor :=
  A : Type u
  B : A → Type u

namespace PFunctor

  instance : Inhabited PFunctor := 
  ⟨⟨default, default⟩⟩

  variable (P : PFunctor) {α β : Type u}

  /-- Applying `P` to an object of `Type` -/
  def Obj (α : Type u)
    := Σ x : P.A, P.B x → α

  /-- Applying `P` to a morphism of `Type` -/
  def map (f : α → β) : P.Obj α → P.Obj β :=
    λ ⟨a, g⟩ => ⟨a, f ∘ g⟩


instance Obj.Inhabited [Inhabited P.A] [Inhabited α] : Inhabited (P.Obj α) :=
 ⟨ ⟨ default, λ _ => default ⟩ ⟩

instance : Functor (P.Obj) where
  map := @map P

protected theorem map_eq (f : α → β) (a : P.A) (g : P.B a → α) :
  @Functor.map (P.Obj) _ _ _ f ⟨a, g⟩ = ⟨a, f ∘ g⟩ :=
rfl

protected theorem id_map : ∀ x : P.Obj α, id <$> x = id x :=
λ ⟨a, b⟩ => rfl

protected theorem comp_map (f : α → β) (g : β → γ) :
  ∀ x : P.Obj α, (g ∘ f) <$> x = g <$> (f <$> x) :=
λ ⟨a, b⟩ => rfl

instance : LawfulFunctor (P.Obj) :=
{
  map_const := rfl,
  id_map := @PFunctor.id_map P, 
  comp_map := @PFunctor.comp_map P
}



/-- `Idx` identifies a location inside the application of a PFunctor.
For `F : PFunctor`, `x : F.Obj α` and `i : F.Idx`, `i` can designate
one part of `x` or is invalid, if `i.1 ≠ x.1` -/
def Idx := Σ x : P.A, P.B x

instance Idx.Inhabited [Inhabited P.A] [Inhabited (P.B default)] : Inhabited P.Idx :=
⟨ ⟨default, default⟩ ⟩

-- Make the variable P implicit
variable {P}

/-- `x.iget i` takes the component of `x` designated by `i` if any is or returns
a default value -/
def Obj.iget [DecidableEq P.A] {α} [_root_.Inhabited α] (x : P.Obj α) (i : P.Idx) : α :=
if h : i.1 = x.1
  then x.2 (cast (congrArg _ h) i.2)
  else default

@[simp]
theorem fst_map {α β : Type u} (x : P.Obj α) (f : α → β) :
  (f <$> x).1 = x.1 := by { cases x; rfl }

@[simp]
theorem iget_map [DecidableEq P.A] {α β : Type u} [Inhabited α] [Inhabited β]
  (x : P.Obj α) (f : α → β) (i : P.Idx)
  (h : i.1 = x.1) :
  (f <$> x).iget i = f (x.iget i) :=
by simp only [Obj.iget, fst_map, *, dif_pos]
   cases x
   rfl 
   


end PFunctor

/-
## Composition of polynomial functors.
-/
namespace PFunctor

/-- functor composition for polynomial functors -/
def comp (P₂ P₁ : PFunctor.{u}) : PFunctor.{u} :=
⟨ Σ a₂ : P₂.1, P₂.2 a₂ → P₁.1,
  λ a₂a₁ => Σ u : P₂.2 a₂a₁.1, P₁.2 (a₂a₁.2 u) ⟩

/-- constructor for composition -/
def comp.mk (P₂ P₁ : PFunctor.{u}) {α : Type} (x : P₂.Obj (P₁.Obj α)) : (comp P₂ P₁).Obj α :=
⟨ ⟨ x.1, Sigma.fst ∘ x.2 ⟩, λ a₂a₁ => (x.2 a₂a₁.1).2 a₂a₁.2  ⟩

/-- destructor for composition -/
def comp.get (P₂ P₁ : PFunctor.{u}) {α : Type} (x : (comp P₂ P₁).Obj α) : P₂.Obj (P₁.Obj α) :=
⟨ x.1.1, λ a₂ => ⟨x.1.2 a₂, λ a₁ => x.2 ⟨a₂,a₁⟩ ⟩ ⟩

end PFunctor

/-
## Lifting predicates and relations.
-/

namespace PFunctor

variable {P : PFunctor.{u}}

open Functor

#check Liftp

theorem liftp_iff {α : Type u} (p : α → Prop) (x : P.Obj α) : 
  Liftp p x ↔ ∃ a f, x = ⟨a, f⟩ ∧ ∀ i, p (f i) 
:= by
  constructor
  · rintro ⟨y, hy⟩
    cases' h : y with a f
    refine' ⟨a, fun i => (f i).val, _, fun i => (f i).property⟩
    rw [← hy, h, PFunctor.map_eq]
    apply congrArg
    rfl
    
  rintro ⟨a, f, xeq, pf⟩
  use ⟨a, fun i => ⟨f i, pf i⟩⟩
  rw [xeq]
  rfl

#check Sigma.mk

theorem liftp_iff' {α : Type u} (p : α → Prop) (a : P.A) (f : P.B a → α) :
    @Liftp.{u} P.Obj _ α p ⟨a, f⟩ ↔ ∀ i, p (f i) := by
  simp only [liftp_iff, Sigma.mk] <;> constructor <;> intro
  · rename_i hex
    cases hex with
    | intro a₂ hex =>
    cases hex with
    | intro f₂ hex =>
    cases hex with 
    | intro left right =>
    cases left;
    assumption
    
  repeat'
    first |
      constructor|
      assumption

theorem liftr_iff {α : Type u} (r : α → α → Prop) (x y : P.Obj α) :
    Liftr r x y ↔ ∃ a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ ∀ i, r (f₀ i) (f₁ i) := by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    cases' h : u with a f
    let f₀ := fun i => (f i).val.fst
    let f₁ := fun i => (f i).val.snd
    use a
    refine ⟨f₀, f₁, ?_⟩
    constructor
    · rw [← xeq, h]
      rfl
      
    constructor
    · rw [← yeq, h]
      rfl
      
    intro i
    exact (f i).property
    
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  refine ⟨⟨a, fun i => ⟨(f₀ i, f₁ i), h i⟩⟩, ?_⟩
  constructor
  · rw [xeq]
    rfl
    
  rw [yeq]
  rfl

open Set

theorem supp_eq {α : Type u} (a : P.A) (f : P.B a → α) : 
  @Supp.{u} P.Obj _ α (⟨a, f⟩ : P.Obj α) = Set.image f Set.univ := 
by
  ext x
  simp only [Supp, image_univ, mem_range, mem_set_of_eq]
  constructor <;> intro h
  · apply @h fun x => ∃ y : P.B a, f y = x
    rw [liftp_iff']
    intro
    refine' ⟨_, rfl⟩
    
  · simp only [liftp_iff', setOf]
    intros p hpfi
    cases h
    subst x
    rename_i w
    apply hpfi w
    

end PFunctor
