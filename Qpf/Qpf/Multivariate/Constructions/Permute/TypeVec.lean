/-
Copyright (c) 2022 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Qpf.Util.TypeVec


namespace TypeVec

  /-- Does the index change corresponding to `permute` -/
  abbrev permute_index {n : Nat} (i : Fin2 n) : Fin2 n → Fin2 n
    | Fin2.fz       => i
    | j@(Fin2.fs k) => if j > i then j
                                else k.weaken

  /-- Move the `i`-th element to the `0`-th position -/
  def permute {n : Nat} (i : Fin2 n) (v : TypeVec n) : TypeVec n
    := fun j => v $ permute_index i j

  /-- Does the index change corresponding to `unpermute` -/
  abbrev unpermute_index {n : Nat} (i j : Fin2 n) : Fin2 n 
  :=
    match n with
      | 0 => by contradiction
      | Nat.succ n =>
        if i = j 
        then 0
        else match j.strengthen with
          | none    => j  -- `i > j` is impossible if `j` is already at the upper bound
          | some js => if i > j then js.add 1
                                else j       

              

/-- Move the `0`-th element to the `i`-th position -/
def unpermute {n : Nat} (i : Fin2 n) (v : TypeVec n) : TypeVec n
  := fun j => v $ unpermute_index i j


@[simp]
theorem permute_index_unpermute_index_eq {n : Nat} {i j : Fin2 n} :
  permute_index i (unpermute_index i j) = j :=
by
  cases n;
  contradiction;
  case succ n =>
  simp [permute_index, unpermute_index]

  by_cases heq : i = j
  <;> simp [heq];
  cases hstr : j.strengthen
  <;> simp [hstr]
  case neg.none => {
    have : j = Fin2.last := Fin2.strengthen_is_none_imp_eq_last hstr;
    cases this;
    have l_gt_i : Fin2.last > i 
    := by rcases lt_trichotomy Fin2.last i with h|h|h
          . apply absurd h; simp; apply Fin2.last_is_maximal;
          . exfalso; apply heq; simp [h]
          . simp [h]
    cases n;
    {
      simp [Fin2.last]
      cases i;
      . rfl
      . contradiction
    } {
      simp [Fin2.last]
      rw [←Fin2.last]
      simp [l_gt_i]
    }
  }
  case neg.some js => {
    by_cases hgt : i > j
    <;> simp [hgt];
    case pos => {
      simp [Fin2.add]
      have : ¬(Fin2.fs js > i) 
      := by have : js.toNat = j.toNat := Eq.symm $ Fin2.strengthen_toNat_eq hstr
            simp[LE.le, Fin2.toNat, this];
            simp[GT.gt, LT.lt, Fin2.toNat] at hgt;
            apply Nat.succ_le_of_lt hgt;
      simp[this]
      apply Fin2.weaken_strengthen_of_some hstr;
    }
    case neg => {
      cases j;
      case fz => {
        exfalso
        have := Decidable.eq_or_lt_of_le $ Fin2.zero_le i;
        rcases this with heq'|hlt;
        . apply heq heq'.symm
        . apply hgt; simp [hlt]
      }
      case fs k => {
        have : Fin2.fs k > i 
        := by cases lt_or_gt_of_ne heq;
              case inl h => simp[h]
              case inr h => contradiction
        simp [this]        
      }
    }
  }


@[simp]
theorem unpermute_index_permute_index_eq {n : Nat} {i j : Fin2 n} :
  unpermute_index i (permute_index i j) = j :=
by
  cases n;
  contradiction;
  case succ n =>
  simp [permute_index, unpermute_index]

  cases j
  <;> simp

  case fz => {
    simp [OfNat.ofNat]
  }

  case fs j => {
    by_cases h₁ : Fin2.fs j > i
    <;> simp [h₁];

    {
      have ne : i ≠ (Fin2.fs j) := ne_of_lt h₁;
      have ngt : ¬i > (Fin2.fs j) := lt_asymm h₁;
      simp [ne, ngt]
      cases (Fin2.fs j).strengthen
      <;> simp;
    }
    case neg => {
      simp at h₁
      cases Decidable.eq_or_lt_of_le h₁;
      case inl eq => {
        cases eq;
        have neq : (Fin2.fs j) ≠ j.weaken := by induction j <;> simp [Fin2.weaken, *];
        simp [Fin2.weaken, neq]
        simp [GT.gt, LT.lt, Fin2.toNat]
        have : ∀m, m < Nat.succ m := fun m => Nat.lt.base m;
        simp [this, Fin2.add]
      }
      case inr lt => {
        have : i > j.weaken := by simp [GT.gt, LT.lt] at lt ⊢;
                                  simp [Fin2.toNat] at lt;
                                  apply lt_trans _ lt
                                  apply Nat.lt.base
        simp [this, ne_of_gt this, Fin2.add];
      }
    }
  }


/-- Proves that `unpermute` is the inverse of `permute` -/
@[simp]
theorem unpermute_permute_id {n : Nat} {i : Fin2 n} {v : TypeVec n} :
  unpermute i (permute i v) = v :=
by
  funext j;
  simp [permute, unpermute]
  apply congrArg
  apply permute_index_unpermute_index_eq;

/-- Proves that `permute` is the inverse of `unpermute` -/
@[simp]
theorem permute_unpermute_id {n : Nat} {i : Fin2 n} {v : TypeVec n} :
  permute i (unpermute i v) = v :=
by
  funext j;
  simp [permute, unpermute]
  apply congrArg
  apply unpermute_index_permute_index_eq; 



/-
  ## Arrows
-/
namespace Arrow
  variable {n : Nat} {α β : TypeVec n}

  def permute (i : Fin2 n) (f : α ⟹ β) : (α.permute i) ⟹ (β.permute i)
    := fun j a => 
          let j' := permute_index i j
          have eq {α} : TypeVec.permute i α j = α j' := by simp[TypeVec.permute];
          let a' := cast eq a;
          let b' := f j' a'
          cast eq.symm b'

  def unpermute (i : Fin2 n) (f : α ⟹ β) : (α.unpermute i) ⟹ (β.unpermute i)
    := fun j a =>
          let j' := unpermute_index i j
          have eq {α} : TypeVec.unpermute i α j = α j' := by simp[TypeVec.unpermute];
          let a' := cast eq a;
          let b' := f j' a'
          cast eq.symm b'

  def unpermute' (i : Fin2 n) (f : (α.permute i) ⟹ (β.permute i)) : α ⟹ β
    := fun j a =>
          let j' := (unpermute_index i j);
          have eq {α} : TypeVec.permute i α j' = α j  
          := by simp[TypeVec.permute]; 
                apply congrArg; 
                apply permute_index_unpermute_index_eq
          -- have eq₂ {α} : TypeVec.unpermute i α j = α j' := by simp[TypeVec.unpermute];
          let a' := cast eq.symm a;
          let b' := f j' a'
          cast eq b'


  /- -/
  theorem unpermute_heq_unpermute' (i : Fin2 n) (f : (α.permute i) ⟹ (β.permute i)) :
    ∀j a a', HEq a a' → HEq (f.unpermute i j a) (f.unpermute' i j a') :=
  by
    intro j a a' heq;
    simp [unpermute, unpermute']
    simp only [heq_cast_left, heq_cast_right];
    apply hcongr
    case H₁ => rfl
    case H₃ => simp
    case H₄ => simp
    
    simp only [heq_cast_left, heq_cast_right];
    apply heq


  /- -/
  theorem unpermute'_permute_id (i : Fin2 n) (f : α ⟹ β) :
    unpermute' i (permute i f) = f :=
  by
    funext j a;
    cases n;
    case zero => contradiction
    case succ n =>

    simp [unpermute', permute];
    apply eq_of_heq;
    simp only [heq_cast_left]

    apply hcongr
    case H₄ => intro; apply congrArg; apply permute_index_unpermute_index_eq;
    case H₃ => apply congrArg; apply permute_index_unpermute_index_eq;
    case H₂ => simp [heq_cast_left]
    
    apply hcongr
    case H₁ => rfl
    case H₃ => rfl
    case H₄ => intro; simp [cast_eq]

    simp;
    apply permute_index_unpermute_index_eq;
      

  @[simp]
  theorem unpermute_permute_heq_ext (f : α ⟹ β) :
    ∀ j a, HEq (unpermute i (permute i f) j a) (f j $ cast (by simp) a) :=
  by
    intro j a;

    have : HEq (unpermute i (permute i f) j a) (unpermute' i (permute i f) j $ cast (by simp) a)
    := by
        conv in a => {
          rw [←(cast_eq (by rfl) a)]
        }
        apply unpermute_heq_unpermute';
        simp [heq_cast_left, heq_cast_right]

    apply HEq.trans this;
    
    apply heq_of_eq;
    apply congrFun;
    apply congrFun;
    apply unpermute'_permute_id;
    

    
    
    

  @[simp]
  theorem unpermute_permute_heq (f : α ⟹ β) :
    HEq (unpermute i (permute i f)) f :=
  by
    have : HEq (cast (β:=(α.permute i).unpermute i ⟹ (β.permute i).unpermute i) (by simp) f) f
    := by simp only [heq_cast_left]; rfl
    
    apply HEq.trans _ this;
    apply heq_of_eq;
    funext a j;
    apply eq_of_heq;

    apply HEq.trans
    apply unpermute_permute_heq_ext;
    simp only [heq_cast_right];

    apply hcongr;
    case H₃ => simp
    case H₄ => simp
    case H₂ => apply cast_heq

    apply hcongr;
    case H₂ => rfl
    case H₃ => rfl
    case H₄ => intro k; simp [cast_eq]

    apply HEq.symm;
    apply cast_heq


  -- theorem permute_unpermute (i : Fin2 n) (f : α ⟹ β) :
  --   HEq (permute i (unpermute i f)) f :=
  -- by
  --   simp [permute, unpermute];


end Arrow

end TypeVec