/-
Copyright (c) 2022 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Qpf.MvFunctor
import Qpf.PFunctor.Multivariate.Basic
import Qpf.PFunctor.Multivariate.M
import Qpf.Qpf.Multivariate.Basic
import Qpf.Qpf.Multivariate.Constructions.Const

namespace MvQpf
  /-- Move the `i`-th argument such that it becomes the last one

      F (a₁, ..., aₙ) = (Permute i F) (a₁, ..., a_ᵢ₋₁, a_ᵢ₊₁, ..., aₙ, aᵢ)
   -/
  def Permute {n : Nat} (i : Fin2 n) (F : TypeVec.{u} n → Type _) : TypeVec.{u} n → Type _
    -- Note that to permute the functor, we *unpermute* its argument
    := fun v => F (v.unpermute i)

  def Unpermute {n : Nat} (i : Fin2 n) (F : TypeVec.{u} n → Type _) : TypeVec.{u} n → Type _
    := fun v => F (v.permute i)

  namespace Permute
    variable {n : Nat} {i : Fin2 n} {F : TypeVec.{u} n → Type _}

    theorem Unpermute_Permute_id :
      Unpermute i (Permute i F) = F :=
    by
      simp only [Permute, Unpermute, TypeVec.unpermute_permute_id]


    def asInner {α : TypeVec n} (a : Permute i F α) : F (α.unpermute i) :=
    by 
      apply cast _ a;
      simp [Permute]

    def ofInner {α : TypeVec n} (a : F α) : Permute i F (α.permute i) :=
    by 
      apply cast _ a;
      simp only [Permute, TypeVec.unpermute_permute_id]

    -- def PermuteArrow {α β : TypeVec n} (f : α ⟹ β)

    instance [func : MvFunctor F] : MvFunctor (Permute i F) where
      map := @fun α β f a => 
        func.map (f.unpermute i) a

    instance [func : MvFunctor F] : MvFunctor (Unpermute i F) where
      map := @fun α β f a => 
        func.map (f.permute i) a


    -- instance [func : MvFunctor F] [qpf : MvQpf F] : MvQpf (Permute i F) where  
    --   P         := qpf.P
    --   abs x     := by _
    --   repr      := _
    --   abs_repr  := _
    --   abs_map   := _
        

  end Permute
      

end MvQpf