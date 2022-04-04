/-
Copyright (c) 2020 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Qpf.MvFunctor
import Qpf.Qpf.Multivariate.Basic

/-!
Projection functors are QPFs. The `n`-ary projection functors on `i` is an `n`-ary
functor `F` such that `F (α₀..αᵢ₋₁, αᵢ, αᵢ₊₁..αₙ₋₁) = αᵢ`
-/


universe u v

namespace MvQpf

open_locale MvFunctor

variable {n : ℕ} (i : Fin2 n)

/-- The projection `i` functor -/
def Prj (v : TypeVec.{u} n) : Type u :=
  v i

instance Prj.inhabited {v : TypeVec.{u} n} [Inhabited (v i)] : Inhabited (Prj i v) :=
  ⟨(default : v i)⟩

/-- `map` on functor `prj i` -/
def Prj.map ⦃α β : TypeVec n⦄ (f : α ⟹ β) : Prj i α → Prj i β :=
  f _

#check @Prj.map
#check @MvFunctor.map

instance Prj.MvFunctor : MvFunctor (Prj i) where
  map := fun {α β} => @Prj.map n i α β

/-- Polynomial representation of the projection functor -/
def Prj.p : MvPFunctor.{u} n where
  A := PUnit
  B := fun _ j => ULift <| PLift <| i = j

/-- Abstraction function of the `qpf` instance -/
def Prj.abs ⦃α : TypeVec n⦄ : (Prj.p i).Obj α → Prj i α
  | ⟨x, f⟩ => f _ ⟨⟨rfl⟩⟩

/-- Representation function of the `qpf` instance -/
def Prj.repr ⦃α : TypeVec n⦄ : 
  Prj i α → (Prj.p i).Obj α 
:= fun x : α i => ⟨⟨⟩, fun j ⟨⟨h⟩⟩ => (cast (congrArg _ h) x)⟩ -- (h.rec (motive := fun _ _ => α j) x)⟩

instance Prj.mvqpf : MvQpf (Prj i) where
  P        := Prj.p i
  abs      := @Prj.abs n i
  repr     := @Prj.repr n i
  abs_repr := by intros; rfl;
  abs_map  := by intros α β f p; cases p; rfl;

end MvQpf

