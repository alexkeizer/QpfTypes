/-
Copyright (c) 2022 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Qpf.Qpf.Multivariate.Constructions.Merge.TypeVec
import Qpf.PFunctor.Multivariate.Basic

variable {n : Nat}

namespace MvPFunctor
  /-- Turn an `n+1`-ary pfunctor into an `n`-ary pfunctor, by identifying the last argument with 
      the `i`-th

      `(P.merge i) (a₁, ..., aₙ) ≃ P (a₁, ..., aₙ, aₙ₋ᵢ)`
   -/
  def merge (i : Fin2 n) (P : MvPFunctor.{u} $ n+1) : MvPFunctor.{u} n := 
    ⟨P.A, fun a => (P.B a).merge i⟩

  section
    variable {P : MvPFunctor $ n+1}

    @[simp]
    theorem merge_B_i {a : P.A} :
      ((merge i P).B a i) = (P.B a (i.fs) ⊕ P.B a Fin2.fz) :=
    by
      simp [merge, TypeVec.merge]

    theorem merge_B_i' {a : P.A} (h : j = i) :
      ((merge i P).B a j) = (P.B a (j.fs) ⊕ P.B a Fin2.fz) :=
    by
      cases h; apply merge_B_i
  end



  section
    variable {i : Fin2 n} (P : MvPFunctor.{u} $ n+1)

    -- Note that the structures of `(P.merge i) (a₁, ..., aₙ)` and `P (a₁, ..., aₙ, aₙ₋ᵢ)` are 
    -- are slightly different, hence they are merely isomorphic and not strictly equivalent.

    def merge_to_duplicate {α : TypeVec.{u} n} : 
      (P.merge i).Obj α → P.Obj (α.duplicate i) :=
    fun ⟨a, f⟩ => ⟨a, fun 
      | Fin2.fz   , x  => f i $ cast (by simp) (Sum.inr (α:=P.B a (i.fs)) x)
      | Fin2.fs j', x  => if h : j' = i
                          then f j' $ cast  (by simp[merge, TypeVec.merge]; cases h; simp) 
                                            (Sum.inl (β:=P.B a (Fin2.fz)) x)
                          else f j' $ cast  (by simp[merge, TypeVec.merge, h]) 
                                            x
    ⟩
    
    def duplicate_to_merge {α : TypeVec.{u} n}:
      P.Obj (α.duplicate i) → (P.merge i).Obj α :=
    fun ⟨a, f⟩ => ⟨a, 
      match n with 
      | 0 => by contradiction 
      | Nat.succ n =>
        fun j x =>
          if h : j = i 
          then match cast (merge_B_i' h) x with
                | Sum.inl x => f _ x
                | Sum.inr x => cast (by cases h; simp) $ f _ x                  
          else 
              f j.fs $ cast (by simp[merge, TypeVec.merge, h]) x
    ⟩

    -- The following two theorems show that these transformations are indeed isomorphisms

    @[simp]
    theorem inverse₁ {α : TypeVec.{u} n} {x : P.Obj (α.duplicate i)} :
      merge_to_duplicate P (duplicate_to_merge P x) = x :=
    by
      cases n
      . contradiction
      case succ n =>

      rcases x with ⟨a, f⟩
      simp[merge_to_duplicate, duplicate_to_merge]
      apply congrArg
      funext j x
      cases j
      <;> simp

      case fz => {
        simp_heq
      }

      case fs j' => {
        by_cases h : j' = i
        <;> simp[h]
        <;> simp_heq
      }

    @[simp]
    theorem inverse₂ {α : TypeVec.{u} n} {x : (P.merge i).Obj α} :
      duplicate_to_merge P (merge_to_duplicate P x) = x :=
    by
      cases n
      . contradiction
      case succ n =>

      rcases x with ⟨a, f⟩
      simp[merge_to_duplicate, duplicate_to_merge]
      apply congrArg
      funext j x
      by_cases h : j=i
      <;> simp [h]
      
      case neg => simp_heq

      case pos => {
        cases h;
        cases hx : cast (β:=B P a (Fin2.fs i) ⊕ B P a Fin2.fz) (by simp) x
        <;> simp
        all_goals
          simp_heq
          apply congrArg;
          have := heq_of_eq hx;
          simp_heq at this;
          apply eq_of_heq;
          simp_heq;
          exact this.symm
      }
       
  end
end MvPFunctor