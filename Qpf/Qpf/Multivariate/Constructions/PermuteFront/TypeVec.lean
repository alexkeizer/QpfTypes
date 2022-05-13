/-
Copyright (c) 2022 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Qpf.Util.TypeVec

/-
  ## TypeVec reordering
-/

namespace TypeVec
/-- Move the `i`-th element to the front -/
def permute_front {n : Nat} (i : Fin2 n) (v : TypeVec n) : TypeVec n
  := fun j => 
        match n with
        | 0 => by contradiction
        | n+1 =>
        let j' := match j.strengthen with
                  | none => i
                  | some k => if j < i then j
                              else Fin2.fs k
        v j'
              

/-- Move the first element to the `i`-th position -/
def unpermute_front {n : Nat} (i : Fin2 n) (v : TypeVec n) : TypeVec n
  := fun j => 
      match n with
      | 0 => by contradiction
      | n+1 =>
      let j' := if j < i       then j
                else if j = i then Fin2.last
                else                match j with
                                    | Fin2.fs j' => j'.weaken   -- subtracts one from j
                                    | 0 => 0  
                                        -- rcases lt_trichotomy Fin2.fz i with h|h|h;
                                        -- . contradiction
                                        -- . contradiction
                                        -- simp [LT.lt, Nat.lt, Fin2.toNat] at h

                                    
      v j'



/-- Proves that `unpermute_front` is the inverse of `permute_front` -/
@[simp]
theorem unpermute_front_permute_front_id {n : Nat} {i : Fin2 n} {v : TypeVec n} :
  unpermute_front i (permute_front i v) = v :=
by
  funext j;
  have not_fz_lt_fz {n : Nat} {i : Fin2 (n+1)} : 
    ¬i < Fin2.fz := by simp [LT.lt, Nat.lt, Fin2.toNat]
  have fz_eq_fz {n : Nat} : @Fin2.fz n = Fin2.fz := by rfl
  have fz_lt_fs {n : Nat} {i : Fin2 n} : Fin2.fz < Fin2.fs i 
  := by simp [LT.lt, Fin2.toNat]; apply Fin2.IsLt.h

  cases n; 
  contradiction;
  simp [permute_front, unpermute_front]
  apply congrArg
  clear v

  cases j
  <;> cases i
  <;> simp [not_fz_lt_fz, fz_eq_fz, fz_lt_fs]
    
  case fz.fs n x => 
    cases n;
    contradiction;
    simp [Fin2.strengthen]

  case fs.fs n x y => {
    by_cases lt : Fin2.fs x < Fin2.fs y
    <;> simp [*]
    . have this : ∃k, Fin2.strengthen (Fin2.fs x) = some k
      := by apply Fin2.strengthen_is_some_of_lt lt;
      rcases this with ⟨k, h_k⟩;
      simp [*]
    .
      have decidable_eq {n : Nat} : DecidableEq (Fin2 n) := by infer_instance;
      cases decidable_eq x y 
      <;> simp [*]
      case neg neq =>
        induction n; 
        case zero => contradiction;    
        case succ n ih =>           
          simp [LT.lt, Fin2.toNat, Fin2.weaken_to_nat_eq_to_nat] at lt |-;
          by_cases Fin2.toNat x < Nat.succ (Fin2.toNat y)
          <;> simp [*]
          exfalso
          apply neq;
          apply Fin2.eq_of_to_nat_eq;
          apply Nat.le_antisymm;
          apply Nat.le_of_succ_le_succ h;
          apply Nat.le_of_succ_le_succ lt;
  }

/-- Proves that `permute_front` is the inverse of `unpermute_front` -/
@[simp]
theorem permute_front_unpermute_front_id {n : Nat} {i : Fin2 n} {v : TypeVec n} :
  permute_front i (unpermute_front i v) = v :=
by
  funext j;

  cases n;
  contradiction;
  simp [permute_front, unpermute_front]
  apply congrArg;
  clear v;
  simp

  cases hj : j.strengthen;
  case none => {
    have : ¬i<i := by simp [LT.lt];
    simp [this]
    apply Eq.symm;
    apply Fin2.strengthen_is_none_imp_eq_last hj;
  }
  case some k => {
    have j_eq_k := Fin2.strengthen_toNat_eq hj;
    by_cases lt : j < i
    <;> simp [*]
    by_cases lt₂ : (Fin2.fs k) < i
    <;> simp [*]
    {
      exfalso;  
      simp [LT.lt, Fin2.toNat] at lt lt₂
      rw [j_eq_k] at lt;          
      have le₂ : Nat.succ (Fin2.toNat k) ≤ Fin2.toNat i
        := Nat.le_of_lt lt₂
      have : Nat.succ (k.toNat) ≤ k.toNat 
        := Nat.le_trans le₂ lt;
      apply Nat.not_succ_le_self _ this
    }
    {
      by_cases Fin2.fs k = i
      <;> simp [*]
      {
        exfalso
        simp [LT.lt, Fin2.toNat] at lt        
        rw [j_eq_k, ←h] at lt;
        simp [Fin2.toNat] at lt
        apply Nat.not_succ_le_self _ lt
      }
      { 
        apply Fin2.weaken_strengthen_of_some;
        assumption
      }
    }
  }


namespace Arrow
  variable {n : Nat} {α β : TypeVec n} (i : Fin2 n)

  /-- Move the `i`-th element to the end -/
  def permute_front (f : α ⟹ β) : (α.permute_front i) ⟹ (β.permute_front i)
    := fun j a => 
          match n with
          | 0 => by contradiction
          | Nat.succ n =>
          match hj : j.strengthen with
          | none =>
            have : ∀ {α : TypeVec (Nat.succ n)}, 
              α.permute_front i j = α i :=
            by  intro α;
                simp [TypeVec.permute_front]
                rw [hj];

            let b' : β i := f i (cast this a)
            cast (Eq.symm this) b'
          | some j' =>
            if lt : j < i then
              have : ∀ {α : TypeVec (Nat.succ n)},
                α.permute_front i j = α j :=
              by
                intro α;
                simp [TypeVec.permute_front]
                rw [hj]; 
                apply congrArg;
                simp[lt];

              let b' : β _ := f j (cast this a)
              cast (Eq.symm this) b'  
            else
              let fs_j := Fin2.fs j'
              have : ∀ {α : TypeVec (Nat.succ n)},
                α.permute_front i j = α (Fin2.fs j') :=
              by
                intro α;
                simp [TypeVec.permute_front]
                rw [hj]; 
                apply congrArg;
                simp[lt];
            let b' : β _ := f fs_j (cast this a)
            cast (Eq.symm this) b'

  /-- Move the last element to the `i`-th position -/
  def unpermute_front (f : α ⟹ β) : (α.unpermute_front i) ⟹ (β.unpermute_front i)
    := fun j a => 
          match n with
          | 0 => by contradiction
          | Nat.succ n =>
          if h₁ : j < i then
            have : ∀ {α : TypeVec (Nat.succ n)}, 
              α.unpermute_front i j = α j :=
            by  intro α;
                simp [TypeVec.unpermute_front];
                apply congrArg;
                simp [h₁];

            let b' : β j := f j (cast this a)
            cast (Eq.symm this) b'

          else if h₂ : j = i then
            have : ∀ {α : TypeVec (Nat.succ n)}, 
              α.unpermute_front i j = α Fin2.last :=
            by
              intro α;
              simp [TypeVec.unpermute_front];
              apply congrArg;
              have : ¬i<i := by exact gt_irrefl i
              simp [h₁, h₂, this];
            
            let b' : β _ := f Fin2.last (cast this a)
            cast (Eq.symm this) b'

          else
            match j with
            | 0 => False.elim $ by 
                rcases lt_trichotomy Fin2.fz i with h|h|h;
                . contradiction
                . contradiction
                simp [LT.lt, Nat.lt, Fin2.toNat] at h
            | Fin2.fs j' =>
            have : ∀ {α : TypeVec (Nat.succ n)}, 
              α.unpermute_front i (Fin2.fs j') = α j'.weaken :=
            by
              intro α;
              simp [TypeVec.unpermute_front];
              apply congrArg;
              have : ¬i<i := by exact gt_irrefl i
              simp [h₁, h₂, this];

            let b' : β _ := f j'.weaken (cast this a)
            cast (Eq.symm this) b'


  /-- Move the last element to the `i`-th position -/
  def unpermute_front' (f : (α.permute_front i) ⟹ (β.permute_front i)) : α ⟹ β
    := fun j a => 
          let f' := f.unpermute_front i;
          let b' := f' j $ cast (by simp) a
          cast (by simp) b'


  theorem Nat.not_lt_x_lt_succ {a b : Nat} :
    a < b → b < (Nat.succ a) → False :=
  by
    intro h₁ h₂;
    induction a generalizing b
    <;> cases b;
    case zero.zero =>      
      apply Nat.lt_irrefl _ h₁

    case zero.succ b =>
      cases b;
      case zero => 
        apply Nat.lt_irrefl _ h₂;
      case succ b =>
        apply Nat.not_lt_zero (Nat.succ b);
        apply Nat.lt_of_succ_lt_succ;
        apply h₂

    case succ.zero a ih =>
      apply Nat.not_lt_zero _ h₁;

    case succ.succ a ih b =>
      apply @ih b;
      apply Nat.lt_of_succ_lt_succ h₁;
      apply Nat.lt_of_succ_lt_succ h₂;
      


  theorem unpermute_front_heq_unpermute_front' {γ : Type _} {j} {h₁} {h₂} (f : (α.permute_front i) ⟹ (β.permute_front i)) :
    ∀ (a : γ), HEq (f.unpermute_front i j $ cast h₁ a) (f.unpermute_front' i j $ cast h₂ a) :=
  by
    intros a;
    match n with
    | 0 => contradiction
    | Nat.succ n =>
    simp [unpermute_front', cast_cast];
    apply HEq.symm;
    simp only [heq_cast_left];
    apply heq_of_eq;
    apply congrArg;
    apply eq_of_heq;
    simp only [heq_cast_left, heq_cast_right]
    rfl


  


  -- TODO: simplify this proof?
  @[simp]
  theorem unpermute_front'_permute_front_id (f : α ⟹ β) :
    unpermute_front' i (permute_front i f) = f :=
  by
    funext j a;
    match n with
    | 0 => contradiction
    | Nat.succ n =>
    simp [unpermute_front', unpermute_front, permute_front];
    apply eq_of_heq;
    by_cases h₁ : j < i
    . have : ∃k, j.strengthen = some k
      := by cases hj : j.strengthen
            case none => {
              exfalso;
              have : j = Fin2.last := Fin2.strengthen_is_none_imp_eq_last hj;
              rw [this] at h₁;
              apply absurd h₁;
              simp;
              apply Fin2.last_is_maximal _;
            }
            case some k => {
              use k
            }
      rcases this with ⟨k, hk⟩;
      simp only [heq_cast_left];
      simp [heq_cast_left, permute_front.match_1, cast_eq, cast_trans, *];
            
      have β_eq : β j = TypeVec.permute_front i β j 
        := by simp [TypeVec.permute_front]; apply congrArg; simp [hk, h₁]
      have β_i_eq_permute (hc : j.strengthen = none) : β i = TypeVec.permute_front i β j
        := by simp[hk] at hc;
      have α_j_eq_α_i (hc : j.strengthen = none) : α j = α i
        := by simp[hk] at hc;

      suffices ∀ js (h : j.strengthen = js), 
      HEq (Option.rec (motive := fun x => Fin2.strengthen j = x → TypeVec.permute_front i β j)
            (fun hj => cast (β_i_eq_permute hj) (f i (cast (α_j_eq_α_i hj) a)))
            (fun val hj => cast β_eq (f j a)) js h
          )
          (f j a)
      from by apply this;

      intro js;
      cases js;
      case none => {
        intro hc;
        simp[hk] at hc
      }
      case some => {
        intro hj';
        simp [Option.rec, heq_cast_left]
      }

    . simp only [heq_cast_left];
      simp [*, heq_cast_left];
      by_cases j_eq_i : j = i;
      {
        simp [j_eq_i, heq_cast_left, permute_front.match_1, cast_trans];
        have last_is_none : (@Fin2.last n).strengthen = none := by simp;

        have β_i_eq : β i = TypeVec.permute_front i β Fin2.last
          := by simp[TypeVec.permute_front]; apply congrArg; simp;
        have α_j_eq_α_i : α j = α i
          := congrArg _ j_eq_i;

        have β_last_eq {k} (hj : (@Fin2.last n).strengthen = some k) : 
          β Fin2.last = TypeVec.permute_front i β Fin2.last :=
        by simp at hj

        have α_j_eq_last {k} (hj : (@Fin2.last n).strengthen = some k) : 
          α j = α Fin2.last :=
        by simp at hj

        have β_val_eq {val k} (hj : (@Fin2.last n).strengthen = some k) : 
          β (Fin2.fs val) = TypeVec.permute_front i β Fin2.last :=
        by simp at hj
        have α_j_eq_val {val k} (hj : (@Fin2.last n).strengthen = some k) : 
          α j = α (Fin2.fs val) :=
        by simp at hj

        suffices ∀ (ls : Option <| Fin2 n) (h : Fin2.strengthen Fin2.last = ls),
          HEq
            (Option.rec (motive := fun x => Fin2.strengthen Fin2.last = x → TypeVec.permute_front i β Fin2.last)
              (fun hj => cast β_i_eq (f i (cast α_j_eq_α_i a)))
              (fun val hj =>
                if h : Fin2.last < i then
                  cast (β_last_eq hj) (f Fin2.last $ cast (α_j_eq_last hj) a)
                else
                  cast (β_val_eq hj) (f (Fin2.fs val) $ cast (α_j_eq_val hj) a)
              )
              ls h
            )
            (f j a)
        from by apply this;
        
        intro ls; 
        intro hj;
        cases ls;
        case pos.some => {
          simp at hj
        }
        case pos.none => {
          skip;
          simp [heq_cast_left];
          cases j_eq_i;
          apply heq_of_eq;
          apply congrFun;
          rfl;
        }
      }
      {
        skip;
        simp [j_eq_i];
        cases j;
        case neg.fz => {
          exfalso;
          simp [LT.lt, Fin2.toNat] at h₁;
          apply absurd _ j_eq_i;
          cases i 
          <;> simp [Fin2.toNat] at h₁;
          rfl
        }
        case neg.fs j' => 
          simp [heq_cast_left, *, permute_front.match_1];
          simp [cast_trans];
          have swj_some : j'.weaken.strengthen = some j' := Fin2.strengthen_weaken_is_some

          /-  The following is a generalization of the current proof state
              it is needed because the default `generalize` strategy does not pick the right motive.
          -/          
          suffices ∀ swj (h : j'.weaken.strengthen = swj),          
            HEq
              (Option.rec (motive := fun x => Fin2.strengthen (Fin2.weaken j') = x → TypeVec.permute_front i β (Fin2.weaken j'))
                (fun hj =>
                  cast (Eq.symm (permute_front.proof_3 n i (Fin2.weaken j') hj))
                    (f i (cast (by simp [swj_some] at hj) a)))
                (fun j'_1 hj =>
                  if h : Fin2.weaken j' < i then
                    cast
                      (Eq.symm
                        (permute_front.proof_4 n i (Fin2.weaken j') j'_1 hj
                          (Eq.mpr_prop (Eq.refl (Fin2.weaken j' < i)) (Eq.mpr_prop (Eq.refl (Fin2.weaken j' < i)) h))))
                      (f (Fin2.weaken j') (@cast (α (@Fin2.fs n j')) (α (@Fin2.weaken n j'))
                          (@Eq.trans (Type _) (α (@Fin2.fs n j')) (@TypeVec.permute_front (Nat.succ n) i α (@Fin2.weaken n j'))
                            (α (@Fin2.weaken n j'))
                            (@Eq.trans (Type _) (α (@Fin2.fs n j'))
                              (@TypeVec.unpermute_front (Nat.succ n) i (@TypeVec.permute_front (Nat.succ n) i α) (@Fin2.fs n j'))
                              (@TypeVec.permute_front (Nat.succ n) i α (@Fin2.weaken n j'))
                              (@TypeVec.Arrow.unpermute_front'.proof_1 (Nat.succ n) α i (@Fin2.fs n j'))
                              (@TypeVec.Arrow.unpermute_front.proof_5 n i j'
                                (@Eq.mpr_not (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.fs n j') i)
                                  (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.fs n j') i)
                                  (@Eq.refl Prop (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.fs n j') i))
                                  (@Eq.mpr_not (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.fs n j') i) False
                                    (@eq_false (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.fs n j') i) h₁)
                                    not_false))
                                (@Eq.mpr_not (@Eq (Fin2 (Nat.succ n)) (@Fin2.fs n j') i)
                                  (@Eq (Fin2 (Nat.succ n)) (@Fin2.fs n j') i)
                                  (@Eq.refl Prop (@Eq (Fin2 (Nat.succ n)) (@Fin2.fs n j') i))
                                  (@Eq.mpr_not (@Eq (Fin2 (Nat.succ n)) (@Fin2.fs n j') i) False
                                    (@eq_false (@Eq (Fin2 (Nat.succ n)) (@Fin2.fs n j') i) j_eq_i) not_false))
                                (@TypeVec.permute_front (Nat.succ n) i α)))
                            (@TypeVec.Arrow.permute_front.proof_4 n i (@Fin2.weaken n j') j'_1 hj
                              (@Eq.mpr_prop (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.weaken n j') i)
                                (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.weaken n j') i)
                                (@Eq.refl Prop (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.weaken n j') i))
                                (@Eq.mpr_prop (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.weaken n j') i)
                                  (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.weaken n j') i)
                                  (@Eq.refl Prop (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.weaken n j') i))
                                  h))
                              α)) a))
                  else
                    cast
                      (Eq.symm
                        (permute_front.proof_5 n i (Fin2.weaken j') j'_1 hj
                          (Eq.mpr_not (Eq.refl (Fin2.weaken j' < i)) (Eq.mpr_not (Eq.refl (Fin2.weaken j' < i)) h))))
                      (f (Fin2.fs j'_1)
                        (cast (@Eq.trans (Type _) (α (@Fin2.fs n j')) (@TypeVec.permute_front (Nat.succ n) i α (@Fin2.weaken n j'))
                          (α (@Fin2.fs n j'_1))
                          (@Eq.trans (Type _) (α (@Fin2.fs n j'))
                            (@TypeVec.unpermute_front (Nat.succ n) i (@TypeVec.permute_front (Nat.succ n) i α) (@Fin2.fs n j'))
                            (@TypeVec.permute_front (Nat.succ n) i α (@Fin2.weaken n j'))
                            (@TypeVec.Arrow.unpermute_front'.proof_1 (Nat.succ n) α i (@Fin2.fs n j'))
                            (@TypeVec.Arrow.unpermute_front.proof_5 n i j'
                              (@Eq.mpr_not (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.fs n j') i)
                                (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.fs n j') i)
                                (@Eq.refl Prop (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.fs n j') i))
                                (@Eq.mpr_not (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.fs n j') i) False
                                  (@eq_false (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.fs n j') i) h₁)
                                  not_false))
                              (@Eq.mpr_not (@Eq (Fin2 (Nat.succ n)) (@Fin2.fs n j') i) (@Eq (Fin2 (Nat.succ n)) (@Fin2.fs n j') i)
                                (@Eq.refl Prop (@Eq (Fin2 (Nat.succ n)) (@Fin2.fs n j') i))
                                (@Eq.mpr_not (@Eq (Fin2 (Nat.succ n)) (@Fin2.fs n j') i) False
                                  (@eq_false (@Eq (Fin2 (Nat.succ n)) (@Fin2.fs n j') i) j_eq_i) not_false))
                              (@TypeVec.permute_front (Nat.succ n) i α)))
                          (@TypeVec.Arrow.permute_front.proof_5 n i (@Fin2.weaken n j') j'_1 hj
                            (@Eq.mpr_not (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.weaken n j') i)
                              (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.weaken n j') i)
                              (@Eq.refl Prop (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.weaken n j') i))
                              (@Eq.mpr_not (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.weaken n j') i)
                                (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.weaken n j') i)
                                (@Eq.refl Prop (@LT.lt (Fin2 (Nat.succ n)) (@Fin2.instLT (Nat.succ n)) (@Fin2.weaken n j') i)) h))
                            α)) 
                          a)))
                swj h)
              (f (Fin2.fs j') a)
          from by apply this;

          -- Proof continues here
          intro swj hj;
          cases swj;
          case none => {
            simp [swj_some] at hj
          }
          case some => {
            simp [*];
            -- exfalso;
            have i_lt : i < (Fin2.fs j') := 
            by
              rcases lt_trichotomy (Fin2.fs j') i with ha|ha|ha;
              . apply absurd ha; assumption
              . apply absurd ha; assumption
              . exact ha;
            by_cases j'_lt : j'.weaken < i
            <;> simp [j'_lt, heq_cast_left];
            {
              exfalso;
              simp [LT.lt, Fin2.toNat] at i_lt j'_lt;
              apply Nat.not_lt_x_lt_succ j'_lt i_lt;
            }
            {
              rw [hj] at swj_some;
              simp at swj_some;
              cases swj_some;
              simp [cast_eq];
            }            
          }
      }



  @[simp]
  theorem unpermute_front_permute_front_heq_ext (f : α ⟹ β) :
    ∀ j a, HEq (unpermute_front i (permute_front i f) j a) (f j $ cast (by simp) a) :=
  by
    intro j a;

    have : HEq (unpermute_front i (permute_front i f) j a) (unpermute_front' i (permute_front i f) j $ cast (by simp) a)
    := by
        conv in a => {
          rw [←(cast_eq (by rfl) a)]
        }
        apply unpermute_front_heq_unpermute_front';

    apply HEq.trans this;
    
    apply heq_of_eq;
    apply congrFun;
    apply congrFun;
    apply unpermute_front'_permute_front_id;
    

    
    
    

  @[simp]
  theorem unpermute_front_permute_front_heq (f : α ⟹ β) :
    HEq (unpermute_front i (permute_front i f)) f :=
  by
    have : HEq (cast (β:=(α.permute_front i).unpermute_front i ⟹ (β.permute_front i).unpermute_front i) (by simp) f) f
    := by simp only [heq_cast_left]; rfl
    
    apply HEq.trans _ this;
    apply heq_of_eq;
    funext a j;
    apply eq_of_heq;

    apply HEq.trans
    apply unpermute_front_permute_front_heq_ext;
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
end Arrow





end TypeVec