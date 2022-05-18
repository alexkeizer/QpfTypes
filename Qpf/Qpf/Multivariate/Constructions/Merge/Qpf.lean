/-
Copyright (c) 2022 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Qpf.MvFunctor
import Qpf.PFunctor.Multivariate.Basic
import Qpf.PFunctor.Multivariate.M
import Qpf.Qpf.Multivariate.Basic

import Qpf.Qpf.Multivariate.Constructions.Merge.TypeVec
import Qpf.Qpf.Multivariate.Constructions.Merge.PFunctor



namespace MvQpf
  /-- Turn an `n+1`-ary qpf into an `n`-ary qpf, by identifying the last argument with 
      the `i+1`-th (counted from the back)

      (F.merge i) (a₁, ..., aₙ) = F (a₁, ..., aₙ, aₙ₋ᵢ)
   -/
  def merge {n : Nat} (i : Fin2 n) (F : TypeVec.{u} (Nat.succ n) → Type _) : TypeVec.{u} n → Type _
    := fun v => F (v.duplicate i)

  namespace merge

    instance [func : MvFunctor F] : MvFunctor (merge i F) where
      map := @fun α β f a => 
        func.map (f.duplicate i) a


    theorem merge_to_duplicate_map {α β : TypeVec n} {P : MvPFunctor (n+1)} {f : α ⟹ β} {x : (P.merge i).Obj α} :
      P.merge_to_duplicate (f <$$> x) = (f.duplicate i) <$$> (P.merge_to_duplicate x) :=
    by
      rcases x with ⟨aₓ, fₓ⟩
      simp [MvFunctor.map, MvPFunctor.map, MvPFunctor.merge_to_duplicate]
      apply congrArg;
      simp [TypeVec.Arrow.duplicate, TypeVec.comp]
      funext j x
      cases j
      <;> simp

      case fs j => {
        by_cases h : j=i
        <;> simp[h]
      }


    variable {n : Nat} {i : Fin2 n} 
    instance [func : MvFunctor F] [qpf : MvQpf F] : MvQpf (merge i F) where
      P         := qpf.P.merge i
      abs       := qpf.abs ∘ qpf.P.merge_to_duplicate
      repr      := qpf.P.duplicate_to_merge ∘ qpf.repr
      abs_repr  := by simp[qpf.abs_repr]
      abs_map   := by intros α β f x
                      simp [merge_to_duplicate_map]
                      simp [qpf.abs_map]
                      simp [MvFunctor.map, MvPFunctor.map]
                      
  end merge

end MvQpf