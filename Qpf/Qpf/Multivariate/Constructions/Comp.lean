/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
import Qpf.PFunctor.Multivariate.Basic
import Qpf.Qpf.Multivariate.Basic

/-!
# The composition of QPFs is itself a QPF

We define composition between one `n`-ary functor and `n` `m`-ary functors
and show that it preserves the QPF structure
-/


universe u

namespace MvQpf

-- open_locale MvFunctor

variable {n m : ℕ} 
         (F : TypeVec.{u} n → Type _) 
         [fF : MvFunctor F] 
         [q : MvQpf F] 
         (G : Fin2 n → TypeVec.{u} m → Type u)
         [fG : ∀ i, (MvFunctor <| G i)] 
         [q' : ∀ i, MvQpf <| G i]

/-- Composition of an `n`-ary functor `F` with `n` `m`-ary
functors `G₁, ..., Gₙ` gives us one `m`-ary functor `F.Comp G` such that 

`F.Comp G (a₁, ..., aₘ) = F ( G₁(a₁, ..., aₘ), ..., Gₙ(a₁, ..., aₘ))`

That is, each argument is broadcasted to each functor
-/
def Comp (v : TypeVec.{u} m) : Type _ :=
  F (fun i => G i v)

namespace Comp

open MvFunctor MvPFunctor

variable {F} {G} {α β : TypeVec.{u} m} (f : α ⟹ β)

instance [I : Inhabited (F fun i : Fin2 n => G i α)] : Inhabited (Comp F G α) :=
  I

/-- Constructor for functor composition -/
protected def mk (x : F fun i => G i α) : (Comp F G) α :=
  x

/-- Destructor for functor composition -/
protected def get (x : (Comp F G) α) : F fun i => G i α :=
  x

@[simp]
protected theorem mk_get (x : (Comp F G) α) : Comp.mk (Comp.get x) = x :=
  rfl

@[simp]
protected theorem get_mk (x : F fun i => G i α) : Comp.get (Comp.mk x) = x :=
  rfl

include fG

/-- map operation defined on a vector of functors -/
protected def map' : (fun i : Fin2 n => G i α) ⟹ fun i : Fin2 n => G i β := fun i => map f

include fF

/-- The composition of functors is itself functorial -/
protected def map : (Comp F G) α → (Comp F G) β :=
  (map fun i => map f : (F fun i => G i α) → F fun i => G i β)


instance instMvFunctor : MvFunctor (Comp F G) where
  map := @fun α β => Comp.map

theorem map_mk (x : F fun i => G i α) : 
  f <$$> Comp.mk x = Comp.mk ((fun i (x : G i α) => f <$$> x) <$$> x) := rfl

theorem get_map (x : Comp F G α) : 
  Comp.get (f <$$> x) = (fun i (x : G i α) => f <$$> x) <$$> Comp.get x := rfl

include q q'

instance instQpf : MvQpf (Comp F G) where
  P := MvPFunctor.Comp (P F) fun i => P <| G i
  abs := @fun α => Comp.mk ∘ (map fun i => abs) ∘ abs ∘ MvPFunctor.Comp.get
  repr := @fun α =>
    MvPFunctor.Comp.mk ∘ repr ∘ (map fun i => (repr : G i α → (fun i : Fin2 n => Obj (P (G i)) α) i)) ∘ Comp.get
  abs_repr := by
    intros
    simp [(· ∘ ·), MvFunctor.map_map, (· ⊚ ·), abs_repr]
  abs_map := by
    intros
    simp [(· ∘ ·)]
    rw [← abs_map]
    simp [MvFunctor.id_map, (· ⊚ ·), map_mk, MvPFunctor.Comp.get_map, abs_map, MvFunctor.map_map, abs_repr]

end Comp

end MvQpf

