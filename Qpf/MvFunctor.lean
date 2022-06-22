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



/-!
  The following is mostly a specialization of `VecClass`, since `MvFunctor` does not fit in the
  `Class : α → Type` signature (it takes an implicit argument). 
-/

/-- A "boxed" type class to express that all elements of `G` implement `MvFunctor` -/
class VecMvFunctor (G : Vec (TypeFun m) n) where
  prop : ∀ i, MvFunctor (G i)

namespace VecMvFunctor


  /-- In case of an empty `Vec`, the statement is vacuous -/
  instance instNil (G : Vec (TypeFun m) 0) : VecMvFunctor G
    := ⟨by intro i; cases i⟩

  /-- 
    The recursive step, if the head and all elements in the tail of a vector implement `Class`,
    then all elements implement `Class`. 
    Requires that `v` is reducible by type class inference.    
  -/
  instance instSucc  (G : Vec (TypeFun m) (.succ n)) 
                              [zero : MvFunctor (G .fz)]
                              /-  It is important that the vector used in the recursive step remains 
                                  reducible, or the inference system will not find the appropriate 
                                  instance. That is why we spell out the composition, rather than 
                                  use the more concise `v ∘ .fs`                              
                              -/
                              [succ : VecMvFunctor (fun i => G i.fs)] : 
                          VecMvFunctor G := 
  ⟨by intro i; 
      cases i; 
      exact zero;
      apply succ.prop
    ⟩


  /-- 
    Alternative recursive step. Since `Vec.append1` is not reducible, we explicitly provide an
    instance
  -/
  instance instAppend1 (tl : Vec (TypeFun m) n) (hd : TypeFun m)
                              [zero : MvFunctor hd]
                              [succ : VecMvFunctor tl] : 
                          VecMvFunctor (tl.append1 hd) := 
  ⟨by intro i; 
      cases i; 
      exact zero;
      apply succ.prop
    ⟩


  -- /-- Users need not be aware of `VecMvFunctor`, they can simply write universally quantified type class 
  --     constraints  -/
  instance instUnbox [inst : VecMvFunctor G] : 
    ∀i, MvFunctor (G i) :=
  inst.prop

  instance instBox [inst : ∀i, MvFunctor (G i)] :
    VecMvFunctor G := ⟨inst⟩

end VecMvFunctor

