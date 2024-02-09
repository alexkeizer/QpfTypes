/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon, Alex Keizer
-/

import Qpf.MathlibPort.Fin2
import Qpf.Util.HEq
-- import Mathlib

universe u v w

abbrev DVec {n : Nat} (αs : Fin2 n → Type u)  : Type _
  := (i : Fin2 n) → αs i

abbrev Vec (α : Type _) (n : Nat)
  := @DVec n fun _ => α

namespace Vec
  def append1 {α : Type u} {n} (tl : Vec α n) (hd : α) : Vec α (.succ n)
    | .fs i   => tl i
    | .fz     => hd

  -- infixl:67 " ::: " => append1

  /-- Drop the last element from a `Vec` -/
  def drop (v : Vec α (n+1)) : Vec α n
    := fun i => v <| .fs i

  def constVec {α : Type _} (a : α) (n : Nat) : Vec α n
    := fun _ => a
end Vec

-- unif_hint (n : Nat) where 
--   |-
--   Fin2 n → Type u =?= Vec.{u+1} (Type u) n
--
-- unif_hint {α : Type _} (n : Nat) where 
--   |- 
--   DVec.{u+1} (Vec.constVec α n) =?= Vec.{u+1} α n

namespace DVec
  /-- Return the last element from a `DVec` -/
  abbrev last (v : @DVec (n+1) αs ) : αs 0
    := v 0

  /-- Drop the last element from a `DVec` -/
  def drop (v : DVec αs) : DVec (Vec.drop αs)
    := fun i => v <| .fs i

  @[reducible]
  def nil : @DVec 0 αs
    := fun emp => by contradiction

  @[reducible]
  def append1 {α : Type u} {αs : Vec (Type u) n} (tl : DVec αs) (hd : α) : DVec (Vec.append1 αs α)
    | .fs i => tl i
    | .fz   => hd
  

  -- infixl:67 " ::: " => append1
end DVec

namespace Vec
  variable {α : Type _} {n : Nat}

  abbrev nil  : Vec α 0           := DVec.nil
  abbrev last : Vec α n.succ → α  := DVec.last
end Vec



/-
  # Notation macros
-/

syntax "myvec[" term,* "]" : term
macro_rules
  | `(myvec[])    => `(Vec.nil)
  | `(myvec[$x])  => `(Vec.append1 myvec[] $x)
  | `(myvec[ $xs,* , $x]) => `(Vec.append1 myvec[$xs,*] $x)



namespace Vec
  theorem drop_append1 {v : Vec α n} {a : α} {i : PFin2 n} : 
      drop (append1 v a) i = v i := 
    rfl

  theorem drop_append1' {v : Vec α n} {a : α} : 
      drop (append1 v a) = v :=
  by funext x; rfl

  theorem last_append1 {v : Vec α n} {a : α} : 
    last (append1 v a) = a
  := rfl

  @[simp]
  theorem append1_drop_last (v : Vec α (n+1)) : append1 (drop v) (last v) = v :=
    funext $ fun i => by cases i; rfl; rfl



  def reverse (v : Vec α n) : Vec α n :=
    fun i => v i.inv


  @[simp]
  theorem reverse_involution {v : Vec α n} :
    v.reverse.reverse = v :=
  by
    funext i;
    dsimp only [reverse]
    apply congrArg;
    simp only [Fin2.inv, PFin2.toFin2_ofFin2_iso, PFin2.inv_involution, PFin2.ofFin2_toFin2_iso]
end Vec


namespace Vec
  /-- Create a `Vec` from a `List`. Note that this conceptually reverses the list, since in a `Vec`
      the 0th index points to the right-most element
   -/
  def ofList : (as : List α) → Vec α (as.length)
    | List.nil        => Vec.nil
    | List.cons a as  => Vec.append1 (ofList as) a
  
  
  /-- Create a `List` from a `Vec`. Note that this conceptually reverses the vector, since in a `Vec`
      the 0th index points to the right-most element
   -/
  def toList : {n : Nat} → Vec α n → List α
    | 0,    _  => List.nil
    | _+1,  v  => List.cons v.last (toList v.drop)


  @[simp]
  theorem toList_length_eq_n {v : Vec α n} : 
    v.toList.length = n :=
  by
    induction n
    case zero => rfl
    case succ n ih =>
      dsimp only [toList, List.length]
      dsimp only [HAdd.hAdd, Add.add, Nat.add]
      apply congrArg
      apply ih

  @[simp]
  theorem ofList_toList_iso {v : Vec α n} :
    HEq (ofList (toList v)) v :=
  by
    apply HEq.trans (b := cast (β:=Vec α (List.length (toList v))) ?hc v);
    case hc =>
      simp only [toList_length_eq_n]
    case h₂ => 
      apply cast_heq
    case h₁ =>
      apply heq_of_eq;
      funext i;
      apply eq_of_heq;
      rw[cast_arg] <;> try (solve | simp);
      simp_heq

      induction n <;> cases i;
      case succ.fz n ih => {
        dsimp[ofList, toList, append1, last, DVec.last]
        apply hcongr <;> (try solve | intros; rfl)
        simp_heq;
        apply hcongr <;> (try solve | intros; rfl)
        simp
      }
      case succ.fs n ih i => {
        dsimp[ofList, toList, append1, drop]
        
        apply HEq.trans (@ih (fun i => v (.fs i)) i);
        apply hcongr <;> (try solve | intros; rfl)
        simp_heq
        apply hcongr;
        case H₂ => apply cast_heq
        case H₃ => apply congrArg; simp
        case H₄ => intro _; apply congrArg; simp
        
        apply hcongr <;> (try solve | intros; rfl);
        simp
      }

  theorem ofList_toList_iso' {v : Vec α n} :
    HEq (fun (j : PFin2.{u} (toList v).length) => ofList (toList v) j.toFin2) 
        (fun (j : PFin2.{u} (toList v).length) => v <| PFin2.toFin2 <| cast (by rw[toList_length_eq_n]) j) :=
  by
    apply HEq.funext
    . rfl
    intro j
    have n_eq : (toList v).length = n := toList_length_eq_n;
    apply hcongr
    . apply ofList_toList_iso
    . intros
      apply hcongr <;> intros <;> (try rw[n_eq])
      . simp_heq
    . intros; simp
    . rw[n_eq]

  @[simp]
  theorem toList_ofList_iso {as : List α} :
    toList (ofList as) = as :=
  by
    induction as;
    case nil          => rfl
    case cons a as ih => simp only [toList, ofList, append1, last, DVec.last, drop, ih]

  instance : Coe (Vec (Type u) n) (TypeVec.{u} n) where
    coe v i := v i

  instance : Coe (TypeVec.{u} n) (Vec (Type u) n) where
    coe v i := v i

  instance : Coe (Fin n → α) (Vec α n) where
    coe f i := f (Fin2.inv i)

end Vec


