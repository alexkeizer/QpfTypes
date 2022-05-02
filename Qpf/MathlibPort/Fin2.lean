/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import Qpf.Mathlib

/-!
# Inductive type variant of `fin`

`Fin` is defined as a subtype of `Nat`. This file defines an equivalent type, `Fin2`, which is
defined inductively. This is useful for its induction principle and different definitional
equalities.

## Main declarations

* `Fin2 n`: Inductive type variant of `Fin n`. `fz` corresponds to `0` and `fs n` corresponds to
  `n`.
* `toNat`, `optOfNat`, `ofNat'`: Conversions to and from `Nat`. `ofNat' m` takes a proof that
  `m < n` through the class `is_lt`.
* `add k`: Takes `i : fin2 n` to `i + k : fin2 (n + k)`.
* `left`: Embeds `fin2 n` into `fin2 (n + k)`.
* `insertPerm a`: Permutation of `fin2 n` which cycles `0, ..., a - 1` and leaves `a, ..., n - 1`
  unchanged.
* `remapLeft f`: Function `fin2 (m + k) → fin2 (n + k)` by applying `f : fin m → fin n` to
  `0, ..., m - 1` and sending `m + i` to `n + i`.
-/


open Nat

universe u

/-- An alternate definition of `fin n` defined as an inductive type instead of a subtype of `Nat`. -/
inductive Fin2 : Nat → Type
  | /-- `0` as a member of `fin (succ n)` (`fin 0` is empty) -/
  fz {n} : Fin2 (succ n)
  | /-- `n` as a member of `fin (succ n)` -/
  fs {n} : Fin2 n → Fin2 (succ n)
  deriving DecidableEq

namespace Fin2

/-- Define a dependent function on `fin2 (succ n)` by giving its value at
zero (`H1`) and by giving a dependent function on the rest (`H2`). -/
-- @[elab_as_eliminator]
protected def cases' {n} {C : Fin2 (succ n) → Sort u} (H1 : C fz) (H2 : ∀ n, C (fs n)) : ∀ i : Fin2 (succ n), C i
  | fz => H1
  | fs n => H2 n

/-- Ex falso. The dependent eliminator for the empty `fin2 0` type. -/
def elim0 {C : Fin2 0 → Sort u} : ∀ i : Fin2 0, C i :=
  fun.

/-- Converts a `fin2` into a natural. -/
def toNat : ∀ {n}, Fin2 n → Nat
  | _, @fz n => 0
  | _, @fs n i => succ (toNat i)

/-- Converts a natural into a `fin2` if it is in range -/
def optOfNat : ∀ {n} k : Nat, Option (Fin2 n)
  | 0, _ => none
  | succ n, 0 => some fz
  | succ n, succ k => fs <$> @optOfNat n k

/-- Converts a natural into a `fin2` given a proof that it is in range -/
def ofNatLt : ∀ {n} (k : Nat) (h : k < n), Fin2 n
  | 0, _, h            => by contradiction
  | succ n, 0, h       => fz
  | succ n, succ k, h  => fs $ @ofNatLt n k (lt_of_succ_lt_succ h)

/-- `i + k : fin2 (n + k)` when `i : fin2 n` and `k : Nat` -/
def add {n} (i : Fin2 n) : ∀ k, Fin2 (n + k)
  | 0 => i
  | succ k => fs (add i k)

/-- `left k` is the embedding `fin2 n → fin2 (k + n)` -/
def left k : ∀ {n}, Fin2 n → Fin2 (k + n)
  | _, @fz n => fz
  | _, @fs n i => fs (left k i)

/-- `insertPerm a` is a permutation of `fin2 n` with the following properties:
  * `insertPerm a i = i+1` if `i < a`
  * `insertPerm a a = 0`
  * `insertPerm a i = i` if `i > a` -/
def insertPerm : ∀ {n}, Fin2 n → Fin2 n → Fin2 n
  | _, @fz n, @fz _ => fz
  | _, @fz n, @fs _ j => fs j
  | _, @fs (succ n) i, @fz _ => fs fz
  | _, @fs (succ n) i, @fs _ j =>
    match insertPerm i j with
    | fz => fz
    | fs k => fs (fs k)

/-- `remapLeft f k : fin2 (m + k) → fin2 (n + k)` applies the function
  `f : fin2 m → fin2 n` to inputs less than `m`, and leaves the right part
  on the right (that is, `remapLeft f k (m + i) = n + i`). -/
def remapLeft {m n} (f : Fin2 m → Fin2 n) : ∀ k, Fin2 (m + k) → Fin2 (n + k)
  | 0, i => f i
  | succ k, @fz _ => fz
  | succ k, @fs _ i => fs (remapLeft f _ i)

/-- This is a simple type class inference prover for proof obligations
  of the form `m < n` where `m n : Nat`. -/
class IsLt (m n : Nat) where
  h : m < n

instance IsLt.zero n : IsLt 0 (succ n) :=
  ⟨succ_pos _⟩

instance IsLt.succ m n [l : IsLt m n] : IsLt (succ m) (succ n) :=
  ⟨succ_lt_succ l.h⟩

/-- Use type class inference to infer the boundedness proof, so that we can directly convert a
`nat` into a `fin2 n`. This supports notation like `&1 : fin 3`. -/
def ofNat' : ∀ {n} m [IsLt m n], Fin2 n
  | 0, m, ⟨h⟩ => absurd h (Nat.not_lt_zero _)
  | succ n, 0, ⟨h⟩ => fz
  | succ n, succ m, ⟨h⟩ => fs (@ofNat' n m ⟨lt_of_succ_lt_succ h⟩)

-- mathport name: «expr& »
local prefix:arg "&" => ofNat'

instance : Inhabited (Fin2 1) :=
  ⟨fz⟩

/-- There is only one function with empty domain `Fin2 0` -/
def eq_fn0 {α} (f g : Fin2 0 → α) : f = g := 
by funext i; cases i

/-- There is only one function with empty domain `Fin2 0`
    We take `Fin2.elim0` to be the "normalized" such function
 -/ 
@[simp] def eq_fn0_elim0 {α} (f g : Fin2 0 → α) : f = Fin2.elim0
  := by apply eq_fn0


/--
  Try to lower the bound on some `Fin2`, which fails iff the value is equal to the upper bound
-/
def strengthen : ∀{n}, Fin2 (succ n) → Option (Fin2 n)
  | 0, _            => none
  | (succ n), fz    => some fz
  | (succ n), fs k  => fs <$> strengthen k


/--
  Weakens the bound on a `Fin2`
-/
def weaken : Fin2 n → Fin2 (succ n)
  | fz   => fz
  | fs k => fs $ weaken k

/--
  The maximal element of `Fin2 (n+1)`, i.e., `n`
-/
def last : {n : Nat} → Fin2 (n+1) 
  | 0   => fz
  | n+1 => fs (@last n)


@[simp]
theorem strengthen_last_is_none {n : Nat} :
  (@Fin2.last n).strengthen = none :=
by
  induction n;
  simp [last]
  simp [strengthen, last, *]


theorem strengthen_is_none_imp_eq_last {n : Nat} {i : Fin2 (n+1)} :
  i.strengthen = none → i = Fin2.last :=
by
  induction n;
  . cases i;
    . simp [strengthen]
    . intros; contradiction
  case succ n ih => 
    simp [strengthen, last, *]
    cases i
    case fz => simp [strengthen]
    case fs i =>
      simp [strengthen, last]
      apply ih;
  

theorem strengthen_toNat_eq {n : Nat} {i : Fin2 (n+1)} {k : Fin2 n} :
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
theorem strengthen_weaken_is_some {n : Nat} {i : Fin2 n} :
  i.weaken.strengthen = some i :=
by
  induction i
  <;> simp [weaken, strengthen, *]

theorem weaken_strengthen_of_some {n : Nat} {i : Fin2 (n+1)} {k : Fin2 n} :
  i.strengthen = some k → k.weaken = i :=
by
  induction k
  <;> cases i
  <;> simp [weaken, strengthen, *]
  case fs ih _ => {
    apply ih
  }


@[simp]
theorem weaken_to_nat_eq_to_nat {n : Nat} (i : Fin2 n) :
  i.weaken.toNat = i.toNat :=
by 
  induction i;
  case fz => rfl
  case fs ih =>
    simp [weaken, toNat, ih];

theorem eq_of_to_nat_eq {n : Nat} (i j : Fin2 n) :
  i.toNat = j.toNat → i = j :=
by
  induction i
  <;> cases j
  <;> simp [toNat]
  case fs x ih y  => {
    apply ih;
  }


/--
  Typeclass instances to make it easier to work with `Fin2`'s
-/
@[simp]
instance (n : Nat) : OfNat (Fin2 (n+1)) (nat_lit 0) := ⟨fz⟩
instance (n : Nat) : OfNat (Fin2 (n+2)) (nat_lit 1) := ⟨fs 0⟩
instance (n : Nat) : OfNat (Fin2 (n+3)) (nat_lit 2) := ⟨fs 1⟩


/-
  ## LT / LE
-/
instance instOrd (n : Nat) : Ord (Fin2 n) where
  compare := (compare ·.toNat ·.toNat)

instance instLT {n : Nat} : LT (Fin2 n) := ⟨(Nat.lt ·.toNat ·.toNat)⟩
instance instLE {n : Nat} : LE (Fin2 n) := ⟨(Nat.le ·.toNat ·.toNat)⟩

instance decidable_lt (n : Nat) : DecidableRel (@LT.lt (Fin2 n) instLT) := fun a b =>
    let d : Decidable (a.toNat < b.toNat) := by infer_instance
    match d with
    | isTrue h  => isTrue  $ by assumption
    | isFalse h => isFalse $ by intro a_lt_b; apply h a_lt_b

instance decidable_le {n : Nat} : DecidableRel (@LE.le (Fin2 n) instLE) := fun a b =>
    let d : Decidable (a.toNat ≤ b.toNat) := by infer_instance
    match d with
    | isTrue h  => isTrue  $ by assumption
    | isFalse h => isFalse $ by intro a_le_b; apply h a_le_b

instance instLinOrd : LinearOrder (Fin2 n) where  
  le_refl _             := by apply Nat.le_refl;
  le_trans _ _ _        := by apply Nat.le_trans;
  lt_iff_le_not_le _ _  := by simp[LT.lt, LE.le]; exact le_of_lt
  le_antisymm x y h₁ h₂ := by simp[LE.le] at h₁ h₂;
                              suffices toNat x = toNat y
                              from by clear h₁ h₂;
                                      induction x 
                                      <;> cases y
                                      <;> simp[toNat] at this;
                                      rfl;
                                      case fs x ih y => {
                                        simp;
                                        apply ih;
                                        apply this;
                                      }
                              apply Nat.le_antisymm h₁ h₂
  le_total _ _          := by apply Nat.le_total
  decidable_le          := decidable_le

def le_refl {n : Nat} : 
  ∀ (x : Fin2 n), x ≤ x := 
  instLinOrd.le_refl

def le_trans {n : Nat} : 
  ∀ (x y z : Fin2 n), x ≤ y → y ≤ z → x ≤ z 
:= instLinOrd.le_trans

def lt_iff_le_not_le : 
  ∀ (x y : Fin2 n), x < y ↔ x ≤ y ∧ ¬y ≤ x 
:= instLinOrd.lt_iff_le_not_le

def le_antisymm : 
  ∀ (x y : Fin2 n), x ≤ y → y ≤ x → x = y
:= instLinOrd.le_antisymm

def le_total :
  ∀ (x y : Fin2 n), x ≤ y ∨ y ≤ x
:= instLinOrd.le_total

def lt_trichotomy {n : Nat}  : 
  ∀(a b : Fin2 n), a < b ∨ a = b ∨ b < a
:= _root_.lt_trichotomy


theorem last_is_maximal {n : Nat} (i : Fin2 (n+1)) :
  i ≤ last :=
by
  induction n;
  case zero =>
    cases i;
    . simp;
    . contradiction
  case succ n ih =>
    cases i;
    . simp [LE.le, toNat]
      apply zero_le 
    . simp [LE.le, toNat] at ih
      apply Nat.succ_le_succ
      apply ih


@[simp]
theorem strengthen_is_some_of_lt {n : Nat} {i j : Fin2 (n+1)} :
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

end Fin2

