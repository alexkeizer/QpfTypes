/-
Copyright (c) 2022 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Qpf.Qpf.Multivariate.Constructions.Permute.TypeVec
import Qpf.PFunctor.Multivariate.Basic

/-
## Permuting the arguments to a pfunctor
-/
namespace MvPFunctor
  variable {n : Nat} (P : MvPFunctor n)

  def permute (i : Fin2 n) : MvPFunctor n :=
    ⟨P.A, fun a => (P.B a).permute i⟩

  variable {P}

  def permute_to_P {α : TypeVec n} {i : Fin2 n} : 
    (P.permute i).Obj α → P.Obj (α.unpermute i) :=
  fun ⟨a, f⟩ => 
    ⟨a, cast (by simp [permute]) $ f.unpermute i⟩

  def P_to_permute {α : TypeVec n} (i : Fin2 n) : 
    P.Obj α → (P.permute i).Obj (α.permute i)  :=
  fun ⟨a, f⟩ => 
    ⟨a, cast (by simp [permute]) $ f.permute i⟩


  @[simp]
  theorem permute_to_P_id_fst {α : TypeVec n} {i : Fin2 n} {a : P.A} {f : (P.B a).permute i ⟹ α.permute i} :
    (permute_to_P ⟨a, f⟩).fst = a :=
  by
    unfold P_to_permute;
    unfold permute_to_P;
    simp;

  @[simp]
  theorem P_to_permute_id_fst {α : TypeVec n} {i : Fin2 n} {a : P.A} {f : P.B a ⟹ α} :
    (P_to_permute i ⟨a, f⟩).fst = a :=
  by
    unfold P_to_permute;
    unfold permute_to_P;
    simp;

  @[simp]
  theorem permute_to_P_to_permute_id_snd  {α : TypeVec n} {i : Fin2 n} 
                                          {a₁ a₂ : P.A} 
                                          {f₁ : P.B a₁ ⟹ α} 
                                          {f₂ : P.B a₂ ⟹ (α.permute i).unpermute i} :
    permute_to_P (P_to_permute i ⟨a₁, f₁⟩) = ⟨a₂, f₂⟩ → HEq f₁ f₂ :=
  by
    unfold P_to_permute;
    unfold permute_to_P;
    simp [cast_eq];
    intro h₁;
    cases h₁;
    simp [heq_cast_right, heq_cast_left];
    apply HEq.symm;
    apply TypeVec.Arrow.unpermute_permute_heq
    
  @[simp]
  theorem permute_to_P_to_permute_id {α : TypeVec n} {i : Fin2 n} {x : P.Obj α} :
    HEq (permute_to_P (P_to_permute i x)) x :=
  by
    rcases h : x with ⟨a, f⟩
    rcases h₂ : permute_to_P (P_to_permute i ⟨a, f⟩) with ⟨a₂, f₂⟩;

    have : a = a₂ 
    := by apply Eq.symm;
          apply Eq.trans (b:=(permute_to_P (P_to_permute i ⟨a, f⟩)).fst);
          . simp [h₂]
          . unfold P_to_permute;
            unfold permute_to_P;
            simp;
    cases this;       

    apply hcongr;
    case H₂ => apply HEq.symm; apply permute_to_P_to_permute_id_snd; assumption;
    case H₃ => simp
    case H₄ => intro a; simp
    case H₁ =>
      apply hcongr;
      case H₂ => rfl
      case H₃ => rfl
      case H₄ => intro a; simp [cast_eq]
      case H₁ =>
        apply hcongr;
        case H₁ => rfl
        case H₂ => simp
        case H₃ => rfl
        case H₄ => intro a; simp [cast_eq]
    
    
    


end MvPFunctor