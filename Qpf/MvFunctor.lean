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
`append_fun f g` : appends a function g to an n-tuple of functions
`drop_fun f`     : drops the last function from an n+1-tuple
`last_fun f`     : returns the last function of a tuple.

Since e.g. `append1 α.drop α.last` is propositionally equal to `α` but not definitionally equal
to it, we need support functions and theorems to mediate between constructions.
-/

import Qpf.Util

universe u v w

class MvFunctor {n : Nat} (F : TypeVec n → Type _) :=
(map : ∀ {α β : TypeVec n}, (α ⟹ β) → (F α → F β))

infixr:100 " <$$> " => MvFunctor.map

namespace MvFunctor


variable {n : Nat} {α β γ : TypeVec.{u} n} {F : TypeVec.{u} n → Type v} [MvFunctor F]

def liftp {α : TypeVec n} (p : ∀ i, α i → Prop) : F α → Prop :=
λ x => ∃ u : F (λ i => Subtype (p i)), (λ i => @Subtype.val _ (p i)) <$$> u = x

def liftr {α β : TypeVec n} (r : ∀ {i}, α i → β i → Prop) : F α → F β → Prop :=
λ x y => ∃ u : F (λ i => {p : α i × β i // r p.fst p.snd}),
  (λ i (t : {p : α i × β i // r p.fst p.snd}) => t.val.fst) <$$> u = x ∧
  (λ i (t : {p : α i × β i // r p.fst p.snd}) => t.val.snd) <$$> u = y

def supp {α : TypeVec n} (x : F α) (i : fin' n) : Set (α i) :=
{ y : α i | ∀ {p}, liftp p x → p i y }

theorem of_mem_supp {α : TypeVec n} {x : F α} {p : ∀ ⦃i⦄, α i → Prop} (h : liftp p x) (i : fin' n):
  ∀ y, y ∈ supp x i → p y :=
λ y hy => hy h


class Lawful {n : Nat} (F : TypeVec n → Type _) [MvFunctor F] : Prop :=
(id_map       : ∀ {α : TypeVec n} (x : F α), TypeVec.id <$$> x = x)
(comp_map     : ∀ {α β γ : TypeVec n} (g : α ⟹ β) (h : β ⟹ γ) (x : F α),
                    (h ⊚ g) <$$> x = h <$$> g <$$> x)

export Lawful (id_map comp_map)
attribute [simp] id_map

variable {n : Nat} {α β γ : TypeVec.{u} n}
variable {F : TypeVec.{u} n → Type v} [MvFunctor F] [Lawful F]

@[simp]
theorem id_map' (x : F α) :
  (λ i a => a) <$$> x = x :=
id_map x

theorem map_map (g : α ⟹ β) (h : β ⟹ γ) (x : F α) :
  h <$$> g <$$> x = (h ⊚ g) <$$> x :=
Eq.symm $ comp_map _ _ _

end MvFunctor