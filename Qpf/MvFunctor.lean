/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Mario Carneiro

Tuples of types, and their categorical structure.

Features:

`TypeVec n`   : n-tuples of types
`α ⟹ β`      : n-tuples of maps
`f ⊚ g`       : composition
`MvFunctor n` : the type class of multivariate functors
`f <$$> x`    : notation for map

Also, support functions for operating with n-tuples of types, such as:

`append1 α β`    : append type `β` to n-tuple `α` to obtain an (n+1)-tuple
`drop α`         : drops the last element of an (n+1)-tuple
`last α`         : returns the last element of an (n+1)-tuple
`appendFun f g` : appends a function g to an n-tuple of functions
`dropFun f`     : drops the last function from an n+1-tuple
`lastFun f`     : returns the last function of a tuple.

Since e.g. `append1 α.drop α.last` is propositionally equal to `α` but not definitionally equal
to it, we need support functions and theorems to mediate between constructions.
-/

import Qpf.Util
import Mathlib

universe u v w

/-- multivariate functors, i.e. functor between the category of type vectors
and the category of Type -/
class MvFunctor {n : Nat} (F : TypeFun n) :=
(map : ∀ {α β : TypeVec n}, (α ⟹ β) → (F α → F β))

infixr:100 " <$$> " => MvFunctor.map

variable {n : Nat} 

namespace MvFunctor

variable {α β γ : TypeVec.{u} n} {F : TypeFun.{u,v} n} [MvFunctor F]

/-- predicate lifting over multivariate functors -/
def Liftp {α : TypeVec n} (p : ∀ i, α i → Prop) : F α → Prop :=
λ x => ∃ u : F (λ i => Subtype (p i)), (λ i => @Subtype.val _ (p i)) <$$> u = x

/-- relational lifting over multivariate functors -/
def Liftr {α β : TypeVec n} (r : ∀ {i}, α i → β i → Prop) : F α → F β → Prop :=
λ x y => ∃ u : F (λ i => {p : α i × β i // r p.fst p.snd}),
  (λ i (t : {p : α i × β i // r p.fst p.snd}) => t.val.fst) <$$> u = x ∧
  (λ i (t : {p : α i × β i // r p.fst p.snd}) => t.val.snd) <$$> u = y

/-- given `x : F α` and a projection `i` of type vector `α`, `supp x i` is the set
of `α.i` contained in `x` -/
def supp {α : TypeVec n} (x : F α) (i : Fin2 n) : Set (α i) :=
{ y : α i | ∀ {p}, Liftp p x → p i y }

theorem of_mem_supp {α : TypeVec n} {x : F α} {p : ∀ ⦃i⦄, α i → Prop} (h : Liftp p x) (i : Fin2 n):
  ∀ y, y ∈ supp x i → p y :=
λ y hy => hy h

end MvFunctor

class LawfulMvFunctor {n : Nat} (F : TypeFun n) [MvFunctor F] : Prop :=
(id_map       : ∀ {α : TypeVec n} (x : F α), TypeVec.id <$$> x = x)
(comp_map     : ∀ {α β γ : TypeVec n} (g : α ⟹ β) (h : β ⟹ γ) (x : F α),
                    (h ⊚ g) <$$> x = h <$$> g <$$> x)

open Nat TypeVec

namespace MvFunctor

export LawfulMvFunctor (id_map comp_map)
open LawfulMvFunctor

attribute [simp] id_map

variable {n : Nat} {α β γ : TypeVec.{u} n}
variable {F : TypeFun.{u,v} n} [MvFunctor F] [LawfulMvFunctor F]


variable (p : α ⟹ Repeat n Prop) (r : α ⊗ α ⟹ Repeat n Prop)

/-- adapt `mvfunctor.liftp` to accept predicates as arrows -/
def Liftp' : F α → Prop :=
MvFunctor.Liftp $ fun i x => ofRepeat $ p i x

/-- adapt `mvfunctor.liftp` to accept relations as arrows -/
def Liftr' : F α → F α → Prop :=
MvFunctor.Liftr $ @fun i x y => ofRepeat $ r i $ TypeVec.Prod.mk _ x y

@[simp]
theorem id_map' (x : F α) :
  (λ i a => a) <$$> x = x :=
id_map x

theorem map_map (g : α ⟹ β) (h : β ⟹ γ) (x : F α) :
  h <$$> g <$$> x = (h ⊚ g) <$$> x :=
Eq.symm $ comp_map _ _ _

section Liftp'

variable (F)

theorem exists_iff_exists_of_mono {p : F α → Prop} 
                                  {q : F β → Prop} 
                                  (f : α ⟹ β) 
                                  (g : β ⟹ α) 
                                  (h₀ : f ⊚ g = TypeVec.id)
                                  (h₁ : ∀ u : F α, p u ↔ q (f <$$> u)) : 
      (∃ u : F α, p u) ↔ ∃ u : F β, q u := 
by
  constructor
  all_goals 
    rintro ⟨u, h₂⟩
  · refine ⟨f <$$> u, ?_⟩
    apply (h₁ u).mp h₂
    
  · refine ⟨g <$$> u, ?_⟩
    apply (h₁ _).mpr _
    simp only [map_map, h₀, id_map, h₂]
    

variable {F}

theorem liftp_def (x : F α) : 
  Liftp' p x ↔ ∃ u : F (Subtype_ p), subtypeVal p <$$> u = x :=
  exists_iff_exists_of_mono F _ _ 
    (to_subtype_of_subtype p)
    (by simp [map_map])

theorem liftr_def (x y : F α) :
    Liftr' r x y ↔
      ∃ u : F (Subtype_ r),
        (TypeVec.Prod.fst ⊚ subtypeVal r) <$$> u = x ∧ (TypeVec.Prod.snd ⊚ subtypeVal r) <$$> u = y :=
  exists_iff_exists_of_mono _ _ _ (to_subtype'_of_subtype' r)
    (by
      simp only [map_map, comp_assoc, subtype_val_to_subtype'] <;> simp [comp])

end Liftp'
end MvFunctor




open Nat

namespace MvFunctor

open TypeVec

section LiftpLastPredIff

variable {F : TypeFun (n + 1)} [_inst_1 : MvFunctor F] [_inst_2 : LawfulMvFunctor F] {α : TypeVec.{u} n}

variable (p : α ⟹ Repeat n Prop) (r : α ⊗ α ⟹ Repeat n Prop)

variable {β : Type u}
variable (pp : β → Prop)

private def f :
    ∀ n α,
      (fun i : Fin2 (n + 1) => { p_1 // ofRepeat (predLast' α pp i p_1) }) ⟹ fun i : Fin2 (n + 1) =>
        { p_1 : (α ::: β) i // predLast α pp p_1 }
  | _, α, Fin2.fs i, x =>
    ⟨x.val,
      cast
        (by
          simp only [predLast] <;> erw [const_iff_true])
        x.property⟩
  | _, α, Fin2.fz, x => ⟨x.val, x.property⟩

private def g :
    ∀ n α,
      (fun i : Fin2 (n + 1) => { p_1 : (α ::: β) i // predLast α pp p_1 }) ⟹ fun i : Fin2 (n + 1) =>
        { p_1 // ofRepeat (predLast' α pp i p_1) }
  | _, α, Fin2.fs i, x =>
    ⟨x.val,
      cast
        (by
          simp only [predLast] <;> erw [const_iff_true])
        x.property⟩
  | _, α, Fin2.fz, x => ⟨x.val, x.property⟩

theorem liftp_last_pred_iff {β} (p : β → Prop) (x : F (α ::: β)) : Liftp' (predLast' _ p) x ↔ Liftp (predLast _ p) x :=
  by
  dsimp only [Liftp, Liftp']
  apply exists_iff_exists_of_mono F (f _ n α) (g _ n α)
  · ext i ⟨x, _⟩
    cases i <;> rfl
    
  · intros u;
    rw [MvFunctor.map_map]
    simp [(· ⊚ ·)];
    suffices (fun i => Subtype.val) = (fun i x => (MvFunctor.f p n α i x).val)
    by rw[this];
    
    ext i ⟨x, _⟩;
    cases i
    <;> rfl
    

open Function

variable (rr : β → β → Prop)

private def f' :
    ∀ n α,
      (fun i : Fin2 (n + 1) => { p_1 : _ × _ // ofRepeat (relLast' α rr i (TypeVec.Prod.mk _ p_1.fst p_1.snd)) }) ⟹
        fun i : Fin2 (n + 1) => { p_1 : (α ::: β) i × _ // relLast α rr p_1.fst p_1.snd }
  | _, α, Fin2.fs i, x =>
    ⟨x.val,
      cast
        (by
          simp only [relLast] <;> erw [repeat_eq_iff_eq])
        x.property⟩
  | _, α, Fin2.fz, x => ⟨x.val, x.property⟩

private def g' :
    ∀ n α,
      (fun i : Fin2 (n + 1) => { p_1 : (α ::: β) i × _ // relLast α rr p_1.fst p_1.snd }) ⟹ fun i : Fin2 (n + 1) =>
        { p_1 : _ × _ // ofRepeat (relLast' α rr i (TypeVec.Prod.mk _ p_1.1 p_1.2)) }
  | _, α, Fin2.fs i, x =>
    ⟨x.val,
      cast
        (by
          simp only [relLast] <;> erw [repeat_eq_iff_eq])
        x.property⟩
  | _, α, Fin2.fz, x => ⟨x.val, x.property⟩

theorem liftr_last_rel_iff (x y : F (α ::: β)) : Liftr' (relLast' _ rr) x y ↔ Liftr (relLast _ rr) x y := by
  dsimp only [Liftr, Liftr']
  apply exists_iff_exists_of_mono F (f' rr _ _) (g' rr _ _)
  · ext i ⟨x, _⟩
    cases i <;> rfl
    
  · intros u;
    simp [MvFunctor.map_map, (· ⊚ ·)]
    suffices  (fun i t => t.val.fst) = ((fun i x => (MvFunctor.f' rr n α i x).val.fst))
            ∧ (fun i t => t.val.snd) = ((fun i x => (MvFunctor.f' rr n α i x).val.snd))
    by  rcases this with ⟨left, right⟩
        simp[left, right];

    constructor
    <;> ext i ⟨x, _⟩
    <;> cases i 
    <;> rfl
    

end LiftpLastPredIff

end MvFunctor