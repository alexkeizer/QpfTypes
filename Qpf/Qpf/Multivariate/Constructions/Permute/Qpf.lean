/-
Copyright (c) 2022 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Qpf.MvFunctor
import Qpf.PFunctor.Multivariate.Basic
import Qpf.PFunctor.Multivariate.M
import Qpf.Qpf.Multivariate.Basic

import Qpf.Qpf.Multivariate.Constructions.Permute.TypeVec
import Qpf.Qpf.Multivariate.Constructions.Permute.PFunctor



namespace MvQpf
  /-- Move the `i`-th argument of a type function `F` such that it becomes the first one

      `F (a₁, ..., aₙ) = (Permute i F) (aᵢ, a₁, ..., a_ᵢ₋₁, a_ᵢ₊₁, ..., aₙ)`
   -/
  def Permute {n : Nat} (i : Fin2 n) (F : TypeVec.{u} n → Type _) : TypeVec.{u} n → Type _
    -- Note that to permute the functor, we *unpermute* its argument
    := fun v => F (v.unpermute i)

  /-- Move the first argument of a type function `F` to the `i`-th position

      `F (a₁, ..., aₙ) = (Unpermute i F) (a₂, ..., a_ᵢ₋₁, a₁, a_ᵢ₊₁, ..., aₙ₋₁, aₙ)`
  -/
  def Unpermute {n : Nat} (i : Fin2 n) (F : TypeVec.{u} n → Type _) : TypeVec.{u} n → Type _
    := fun v => F (v.permute i)

  namespace Permute
    variable {n : Nat} {i : Fin2 n} {F : TypeVec.{u} n → Type _}

    /-- Proves that `Unpermute` is the inverse of `Permute` -/
    theorem Unpermute_Permute_id :
      Unpermute i (Permute i F) = F :=
    by
      simp only [Permute, Unpermute, TypeVec.unpermute_permute_id]

    /-- The permuted function is a functor when `F` is a functor -/
    instance [func : MvFunctor F] : MvFunctor (Permute i F) where
      map := @fun α β f a => 
        func.map (f.unpermute i) a

    instance [func : MvFunctor F] : MvFunctor (Unpermute i F) where
      map := @fun α β f a => 
        func.map (f.permute i) a



    /-- The permuted function is a qpf when `F` is a qpf -/
    instance [func : MvFunctor F] [qpf : MvQpf F] : MvQpf (Permute i F) where  
      P           := qpf.P.permute i
      abs         := qpf.abs ∘ qpf.P.permute_to_P
      repr        := (cast (by simp)) ∘ qpf.P.P_to_permute i ∘ qpf.repr
      abs_repr x  := by simp
                        conv => {
                          rhs
                          rw [←qpf.abs_repr x]
                        }
                        apply congrArg
                        apply eq_of_heq
                        apply HEq.trans _
                        apply MvPFunctor.permute_to_P_to_permute_id (i:=i)
                        apply hcongr;
                        case H₁ => {
                          apply hcongr;
                          case H₂ => rfl
                          case H₃ => rfl
                          case H₄ => simp [cast_eq]

                          apply hcongr;
                          case H₂ => simp
                          case H₃ => rfl
                          case H₄ => simp [cast_eq]

                          rfl
                        }
                        all_goals
                          simp [cast_heq]

      abs_map     := by intro α β f p;
                        rcases h₁ : p with ⟨a₁, f₁⟩
                        simp [MvFunctor.map, MvPFunctor.map]
                        conv => {
                          rhs;
                          rw [←qpf.abs_map]
                        }
                        apply congrArg;
                        simp [MvFunctor.map, MvPFunctor.map];
                        rcases h₂ : MvPFunctor.permute_to_P ⟨a₁, f₁⟩ with ⟨a₂, f₂⟩;
                        simp
                        unfold MvPFunctor.permute_to_P;
                        unfold MvPFunctor.permute_to_P at h₂
                        simp at h₂;
                        cases h₂;
                        simp
                        apply congrArg;
                        unfold TypeVec.comp;

                        apply eq_of_heq;
                        simp only [TypeVec.Arrow.unpermute]
                        simp_heq;

                        apply heq_of_eq';
                        case h => {
                          simp [MvPFunctor.permute]  
                        }
                        funext j x;
                        repeat 
                          rw [cast_arg']
                          case h₂ => simp
                        repeat
                          rw [cast_arg]
                          any_goals simp;
                        
                        apply eq_of_heq
                        simp_heq
                        apply HEq.rfl

  end Permute
      

end MvQpf