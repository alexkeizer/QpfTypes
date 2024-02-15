/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import Mathlib.Data.Fin.Fin2
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Init.Order.Defs

/-!
# Inductive type variant of `Fin`

`Fin` is defined as a subtype of `Nat`. This file defines an equivalent type, `PFin2`, which is
defined inductively, and is universe polymorphic. This is useful for its induction principle and 
different definitional equalities.


## Main declarations

* `PFin2 n`: Inductive and universe polymorphic type variant of `Fin n`. `fz` corresponds to `0` and 
  `fs n` corresponds to `n`.
* `Fin2 n`: shorthand for `PFin2.{0} n`, i.e., it lives in `Type`
* `toNat`, `optOfNat`, `ofNat'`: Conversions to and from `Nat`. `ofNat' m` takes a proof that
  `m < n` through the class `is_lt`.
* `add k`: Takes `i : PFin2 n` to `i + k : PFin2 (n + k)`.
* `left`: Embeds `PFin2 n` into `PFin2 (n + k)`.
* `insertPerm a`: Permutation of `PFin2 n` which cycles `0, ..., a - 1` and leaves `a, ..., n - 1`
  unchanged.
* `remapLeft f`: Function `PFin2 (m + k) → PFin2 (n + k)` by applying `f : PFin2 m → PFin2 n` to
  `0, ..., m - 1` and sending `m + i` to `n + i`.
-/


open Nat

universe u

/-- An alternate definition of `fin n` defined as an inductive type instead of a subtype of `Nat`. -/
inductive PFin2 : Nat → Type u
  | /-- `0` as a member of `fin (succ n)` (`fin 0` is empty) -/
  fz {n} : PFin2 (succ n)
  | /-- `n` as a member of `fin (succ n)` -/
  fs {n} : PFin2 n → PFin2 (succ n)
  deriving DecidableEq

namespace PFin2

/-- Define a dependent function on `PFin2 (succ n)` by giving its value at
zero (`H1`) and by giving a dependent function on the rest (`H2`). -/
-- @[elab_as_eliminator]
protected def cases' {n} {C : PFin2 (succ n) → Sort u} (H1 : C fz) (H2 : ∀ n, C (fs n)) : ∀ i : PFin2 (succ n), C i
  | fz => H1
  | fs n => H2 n

/-- Ex falso. The dependent eliminator for the empty `PFin2 0` type. -/
def elim0 {C : PFin2 0 → Sort u} : ∀ i : PFin2 0, C i :=
  by intro i; cases i

/-- Converts a `PFin2` into a natural. -/
def toNat : ∀ {n}, PFin2 n → Nat
  | _, @fz _ => 0
  | _, @fs _ i => succ (toNat i)

/-- Shows that `toNat` produces a natural withing the range -/
theorem toNat_in_range (i : PFin2 n) :
  i.toNat < n :=
by
  induction i
  case fz       => apply succ_pos
  case fs _ ih  => apply lt_succ_of_le ih


theorem toNat_inj {i j : PFin2 n} :
  i.toNat = j.toNat → i = j :=
by
  intro h
  induction i
  <;> cases j
  case fz.fz => 
    rfl
  case fs.fs i ih j =>
    simp only [toNat, Nat.succ.injEq] at h
    specialize ih h
    cases ih
    rfl
  case fs.fz | fz.fs =>
    simp only [toNat] at h

/-- Converts a `PFin2` into the a `Fin` -/
def toFin : PFin2 n → Fin n
  := fun i => ⟨i.toNat, toNat_in_range i⟩


/-- Converts a natural into a `PFin2` if it is in range -/
def optOfNat : ∀ {n} (_ : Nat), Option (PFin2 n)
  | 0, _ => none
  | succ _, 0 => some fz
  | succ n, succ k => fs <$> @optOfNat n k

/-- Converts a natural into a `PFin2` given a proof that it is in range -/
def ofNatLt : ∀ {n} (k : Nat) (_ : k < n), PFin2 n
  | 0, _, h            => by contradiction
  | succ n, 0, _       => fz
  | succ n, succ k, h  => fs $ @ofNatLt n k (lt_of_succ_lt_succ h)


/-- Converts a `Fin` into a `PFin2` -/
def ofFin : Fin n → PFin2 n
  := fun ⟨i, h⟩ => ofNatLt i h


/-- `i + k : PFin2 (n + k)` when `i : PFin2 n` and `k : Nat` -/
def add {n} (i : PFin2 n) : ∀ k, PFin2 (n + k)
  | 0 => i
  | succ k => fs (add i k)

/-- `left k` is the embedding `PFin2 n → PFin2 (k + n)` -/
def left k : ∀ {n}, PFin2 n → PFin2 (k + n)
  | _, fz => fz
  | _, fs i => fs (left k i)

/-- `insertPerm a` is a permutation of `PFin2 n` with the following properties:
  * `insertPerm a i = i+1` if `i < a`
  * `insertPerm a a = 0`
  * `insertPerm a i = i` if `i > a` -/
def insertPerm : ∀ {n}, PFin2 n → PFin2 n → PFin2 n
  | _, fz, fz => fz
  | _, fz, fs j => fs j
  | _, @fs (succ _) _, @fz _ => fs fz
  | _, @fs (succ _) i, @fs _ j =>
    match insertPerm i j with
    | fz => fz
    | fs k => fs (fs k)

/-- `remapLeft f k : PFin2 (m + k) → PFin2 (n + k)` applies the function
  `f : PFin2 m → PFin2 n` to inputs less than `m`, and leaves the right part
  on the right (that is, `remapLeft f k (m + i) = n + i`). -/
def remapLeft {m n} (f : PFin2 m → PFin2 n) : ∀ k, PFin2 (m + k) → PFin2 (n + k)
  | 0, i => f i
  | succ _, @fz _ => fz
  | succ _, @fs _ i => fs (remapLeft f _ i)

/-- This is a simple type class inference prover for proof obligations
  of the form `m < n` where `m n : Nat`. -/
class IsLt (m n : Nat) where
  h : m < n

instance IsLt.zero n : IsLt 0 (succ n) :=
  ⟨succ_pos _⟩

instance IsLt.succ m n [l : IsLt m n] : IsLt (succ m) (succ n) :=
  ⟨succ_lt_succ l.h⟩

/-- Use type class inference to infer the boundedness proof, so that we can directly convert a
`nat` into a `PFin2 n`. This supports notation like `&1 : fin 3`. -/
def ofNat' : ∀ {n} m [IsLt m n], PFin2 n
  | 0, _, ⟨h⟩ => absurd h (Nat.not_lt_zero _)
  | succ _, 0, ⟨_⟩ => fz
  | succ n, succ m, ⟨h⟩ => fs (@ofNat' n m ⟨lt_of_succ_lt_succ h⟩)

-- mathport name: «expr& »
local prefix:arg "&" => ofNat'

instance : Inhabited (PFin2 1) :=
  ⟨fz⟩

/-- There is only one function with empty domain `PFin2 0` -/
def eq_fn0 {α} (f g : PFin2 0 → α) : f = g := 
by funext i; cases i

/-- There is only one function with empty domain `PFin2 0`
    We take `PFin2.elim0` to be the "normalized" such function
 -/ 
@[simp] def eq_fn0_elim0 {α} (f _g : PFin2 0 → α) : f = PFin2.elim0
  := by apply eq_fn0


/--
  Try to lower the bound on some `PFin2`, which fails iff the value is equal to the upper bound
-/
def strengthen : ∀{n}, PFin2 (succ n) → Option (PFin2 n)
  | 0, _            => none
  | (succ _), fz    => some fz
  | (succ _), fs k  => fs <$> strengthen k


/--
  Weakens the bound on a `PFin2`, without changing the value
-/
def weaken : PFin2 n → PFin2 (succ n)
  | fz   => fz
  | fs k => fs $ weaken k

/--
  Decrements a `PFin2` by one, simultaneously lowering the bound
-/
def decr : PFin2 (Nat.succ $ Nat.succ n) → PFin2 (Nat.succ n)
  | fz    => fz
  | fs j  => j

/--
  The maximal element of `PFin2 (n+1)`, i.e., `n`
-/
def last : {n : Nat} → PFin2 (n+1) 
  | 0   => fz
  | n+1 => fs (@last n)

/--
  The inverse of `i` w.r.t. addition modulo `n`, i.e., .last - i
-/
def inv : {n : Nat} → PFin2.{u} n → PFin2.{u} n
  | 0,    _     => by contradiction
  | 1,    .fs _ => by contradiction
  | n+1,  .fz   => last
  | n+2,  .fs i => i.inv.weaken


@[simp]
theorem strengthen_last_is_none {n : Nat} :
  (@last n).strengthen = none :=
by
  induction n
  . simp [strengthen, last]
  . simp [strengthen, last, *]


theorem strengthen_is_none_imp_eq_last {n : Nat} {i : PFin2 (n+1)} :
  i.strengthen = none → i = last :=
by
  induction n;
  . cases i;
    . simp [strengthen, last]
    . intros; contradiction
  case succ n ih => 
    simp [strengthen, last, *]
    cases i
    case fz => simp [strengthen]
    case fs i =>
      simp [strengthen, last]
      apply ih;
  

theorem strengthen_toNat_eq {n : Nat} {i : PFin2 (n+1)} {k : PFin2 n} :
  i.strengthen = some k → i.toNat = k.toNat :=
by 
  intro h;
  induction k
  <;> cases i
  . simp [toNat]
  . simp [strengthen] at h
  . simp [strengthen] at h
  . simp [strengthen] at h
    simp [toNat, *]


@[simp]
theorem strengthen_weaken_is_some {n : Nat} {i : PFin2 n} :
  i.weaken.strengthen = some i :=
by
  induction i
  <;> simp [weaken, strengthen, *]

theorem weaken_strengthen_of_some {n : Nat} {i : PFin2 (n+1)} {k : PFin2 n} :
  i.strengthen = some k → k.weaken = i :=
by
  induction k
  <;> cases i
  <;> simp [weaken, strengthen, *]
  case fs ih _ => {
    apply ih
  }


@[simp]
theorem weaken_to_nat_eq_to_nat {n : Nat} (i : PFin2 n) :
  i.weaken.toNat = i.toNat :=
by 
  induction i;
  case fz => rfl
  case fs ih =>
    simp [weaken, toNat, ih];

theorem eq_of_to_nat_eq {n : Nat} (i j : PFin2 n) :
  i.toNat = j.toNat → i = j :=
by
  induction i
  <;> cases j
  <;> simp [toNat]
  case fs x ih y  => {
    apply ih;
  }


theorem inv_last_eq_fz {n : Nat} :
  (@last n).inv = .fz :=
by
  induction n <;> simp [inv, last, weaken, *]

theorem inv_weaken_eq_fs_inv {n : Nat} (i : PFin2 n):
  inv (weaken  i) = .fs (inv i) :=
by
  induction i
  <;> simp[inv, weaken, last]
  case fs n i ih =>
    simp[ih]
    cases n
    . contradiction
    . simp[inv, weaken]
    

@[simp]
theorem inv_involution {i : PFin2 n} :
  i.inv.inv = i :=
by
    induction i
    simp [inv]
    case fz => apply inv_last_eq_fz
    case fs n i ih => {
      cases n;
      case zero => contradiction
      case succ n =>
        simp[inv]
        rw[inv_weaken_eq_fs_inv i.inv]
        apply congrArg
        apply ih
    }


    -- case zero.fs => contradiction
    -- case succ.fs => simp[inv_last_eq_fz, weaken]


/--
  Typeclass instances to make it easier to work with `PFin2`'s
-/
@[simp]
instance (n : Nat) : OfNat (PFin2 (n+1)) (nat_lit 0) := ⟨fz⟩
instance (n : Nat) : OfNat (PFin2 (n+2)) (nat_lit 1) := ⟨fs 0⟩
instance (n : Nat) : OfNat (PFin2 (n+3)) (nat_lit 2) := ⟨fs 1⟩


/-
  ## LT / LE
-/
instance instOrd (n : Nat) : Ord (PFin2 n) where
  compare := (compare ·.toNat ·.toNat)

instance instLT {n : Nat} : LT (PFin2 n) := ⟨(Nat.lt ·.toNat ·.toNat)⟩
instance instLE {n : Nat} : LE (PFin2 n) := ⟨(Nat.le ·.toNat ·.toNat)⟩

instance decidable_lt (n : Nat) : DecidableRel (@LT.lt (PFin2 n) instLT) := fun a b =>
    let d : Decidable (a.toNat < b.toNat) := by infer_instance
    match d with
    | isTrue h  => isTrue  $ by assumption
    | isFalse h => isFalse $ by intro a_lt_b; apply h a_lt_b

instance decidable_le {n : Nat} : DecidableRel (@LE.le (PFin2 n) instLE) := fun a b =>
    let d : Decidable (a.toNat ≤ b.toNat) := by infer_instance
    match d with
    | isTrue h  => isTrue  $ by assumption
    | isFalse h => isFalse $ by intro a_le_b; apply h a_le_b

instance instLinOrd : LinearOrder (PFin2 n) where
  le_refl _             := by apply Nat.le_refl;
  le_trans _ _ _        := by apply Nat.le_trans;
  lt_iff_le_not_le _ _  := by simp[LT.lt, LE.le]; exact le_of_lt
  le_antisymm x y h₁ h₂ := by simp[LE.le] at h₁ h₂;
                              suffices toNat x = toNat y
                              from by clear h₁ h₂;
                                      induction x 
                                      <;> cases y
                                      <;> simp [toNat] at this;
                                      case fz => rfl
                                      case fs x ih y => {
                                        simp;
                                        apply ih;
                                        apply this;
                                      }
                              apply Nat.le_antisymm h₁ h₂
  le_total _ _          := by apply Nat.le_total
  decidableLE          := decidable_le
  compare_eq_compareOfLessAndEq := by 
    intro x y
    simp only [compare, instOrd, compareOfLessAndEq]
    conv => {
      arg 2
      simp[LT.lt]
    }
    by_cases h : (toNat x < toNat y)
    <;> simp [h, ite_true, ite_false]
    by_cases h : x = y
    {
      cases h
      simp only [ite_true]
    }
    {
      suffices ¬(toNat x = toNat y)
      from by simp only [ite_false, this, h]
      intro contra
      have : x = y := toNat_inj contra
      contradiction
    }
    

    


def le_refl {n : Nat} : 
  ∀ (x : PFin2 n), x ≤ x := 
  instLinOrd.le_refl

def le_trans {n : Nat} : 
  ∀ (x y z : PFin2 n), x ≤ y → y ≤ z → x ≤ z 
:= instLinOrd.le_trans

def lt_iff_le_not_le : 
  ∀ (x y : PFin2 n), x < y ↔ x ≤ y ∧ ¬y ≤ x 
:= instLinOrd.lt_iff_le_not_le

def le_antisymm : 
  ∀ (x y : PFin2 n), x ≤ y → y ≤ x → x = y
:= instLinOrd.le_antisymm

def le_total :
  ∀ (x y : PFin2 n), x ≤ y ∨ y ≤ x
:= instLinOrd.le_total

def lt_trichotomy {n : Nat}  : 
  ∀(a b : PFin2 n), a < b ∨ a = b ∨ b < a
:= _root_.lt_trichotomy

def zero_le {n : Nat} (i : PFin2 (n+1)) :
  .fz ≤ i :=
by
  simp [LE.le, toNat];
  apply Nat.zero_le


theorem last_is_maximal {n : Nat} (i : PFin2 (n+1)) :
  i ≤ last :=
by
  induction n;
  case zero =>
    cases i;
    . simp [last];
    . contradiction
  case succ n ih =>
    cases i;
    . simp [LE.le, toNat]
      apply Nat.zero_le 
    . simp [LE.le, toNat] at ih
      apply Nat.succ_le_succ
      apply ih


@[simp]
theorem strengthen_is_some_of_lt {n : Nat} {i j : PFin2 (n+1)} :
  i < j → ∃k, i.strengthen = some k :=
by
  intro lt;
  cases h : strengthen i;
  case some => simp
  case none =>
    have : i = last := by apply strengthen_is_none_imp_eq_last h;
    cases this;
    have : j ≤ last   := by apply last_is_maximal;
    have : ¬ last < j := by simp[this];
    contradiction



  def ofFin2 : Fin2 n → PFin2 n
    | .fz   => .fz
    | .fs i => .fs <| ofFin2 i

  def toFin2 : PFin2 n → Fin2 n
    | .fz   => .fz
    | .fs i => .fs <| toFin2 i

  @[simp]
  theorem ofFin2_toFin2_iso {i : Fin2 n} :
    (toFin2 <| ofFin2 i) = i :=
  by 
    induction i
    . rfl
    . simp [ofFin2, toFin2, *]

  @[simp]
  theorem toFin2_ofFin2_iso {i : PFin2 n} :
    (ofFin2 <| toFin2 i) = i :=
  by 
    induction i
    . rfl
    . simp [ofFin2, toFin2, *]

  instance : Coe (Fin2 n) (PFin2 n) := ⟨ofFin2⟩
  instance : Coe (PFin2 n) (Fin2 n) := ⟨toFin2⟩

  instance : Coe (PFin2 n) (Fin n) := ⟨toFin⟩
  instance : Coe (Fin n) (PFin2 n) := ⟨ofFin⟩

  instance : Coe (Fin n) (Fin2 n) := ⟨fun i => toFin2 <| ofFin.{0} i⟩
  instance : Coe (Fin2 n) (Fin n) := ⟨fun i => toFin <| ofFin2.{0} i⟩

end PFin2


namespace Fin2
  /--
  Typeclass instances to make it easier to work with `PFin2`'s
-/
@[simp]
instance (n : Nat) : OfNat (Fin2 (n+1)) (nat_lit 0) := ⟨fz⟩
instance (n : Nat) : OfNat (Fin2 (n+2)) (nat_lit 1) := ⟨fs 0⟩
instance (n : Nat) : OfNat (Fin2 (n+3)) (nat_lit 2) := ⟨fs 1⟩

  def inv : Fin2 n → Fin2 n
    := fun i => (PFin2.inv.{0} i : PFin2 n)

end Fin2
