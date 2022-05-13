/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
import Qpf.Qpf.Multivariate.Basic
import Qpf.MathlibPort.Quot

/-!
# The quotient of QPF is itself a QPF

The quotients are here defined using a surjective function and
its right inverse. They are very similar to the `abs` and `repr`
functions found in the definition of `mvqpf`
-/


universe u

open_locale MvFunctor

namespace MvQpf

variable {n : ℕ}

variable {F : TypeVec.{u} n → Type u}

section repr

variable [MvFunctor F] [q : MvQpf F]

variable {G : TypeVec.{u} n → Type u} [MvFunctor G]

variable {FG_abs : ∀ {α}, F α → G α}

variable {FG_repr : ∀ {α}, G α → F α}


/-- If `F` is a QPF then `G` is a QPF as well. Can be used to
construct `mvqpf` instances by transporting them across
surjective functions -/
def quotientQpf (FG_abs_repr : ∀ {α} x : G α, FG_abs (FG_repr x) = x)
    (FG_abs_map : ∀ {α β} (f : α ⟹ β) (x : F α), FG_abs (f <$$> x) = f <$$> FG_abs x) : MvQpf G where
  P := q.P
  abs := @fun α p         => FG_abs (abs p)
  repr := @fun α x        => repr (FG_repr x)
  abs_repr := @fun α x    => by simp [abs_repr, FG_abs_repr]
  abs_map := @fun α β f p => by simp [abs_map, FG_abs_map]

end repr

section Rel

variable (R : ∀ ⦃α⦄, F α → F α → Prop)

/-- Functorial quotient type -/
def Quot1 (α : TypeVec n) :=
  Quot (@R α)

instance Quot1.inhabited {α : TypeVec n} [Inhabited <| F α] : Inhabited (Quot1 R α) :=
  ⟨Quot.mk _ default⟩

variable [MvFunctor F] [q : MvQpf F]

variable (Hfunc : ∀ ⦃α β⦄ (a b : F α) (f : α ⟹ β), R a b → R (f <$$> a) (f <$$> b))

/-- `map` of the `quot1` functor -/
def Quot1.map ⦃α β⦄ (f : α ⟹ β) : Quot1.{u} R α → Quot1.{u} R β :=
  (Quot.lift fun x : F α => Quot.mk _ (f <$$> x : F β)) fun a b h => Quot.sound <| Hfunc a b _ h


/-- `MvFunctor` instance for `quot1` with well-behaved `R` -/
def Quot1.MvFunctor : MvFunctor (Quot1 R) where
  map := @(Quot1.map R Hfunc)


/-- `quot1` is a qpf -/
noncomputable def relQuot : @MvQpf _ (Quot1 R) (MvQpf.Quot1.MvFunctor R Hfunc) :=
  @quotientQpf n F _ q _ (MvQpf.Quot1.MvFunctor R Hfunc) 
                         (@fun α x => Quot.mk _ x) 
                         (@fun α => Quot.out)
                         (@fun α x => Quot.out_eq _) 
                         (@fun α β f x => rfl)

end Rel

end MvQpf

