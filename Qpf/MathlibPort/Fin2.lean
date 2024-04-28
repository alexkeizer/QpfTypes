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

-- universe u
--
-- /-- An alternate definition of `fin n` defined as an inductive type instead of a subtype of `Nat`. -/
-- inductive PFin2 : Nat → Type u
--   | /-- `0` as a member of `fin (succ n)` (`fin 0` is empty) -/
--   fz {n} : PFin2 (succ n)
--   | /-- `n` as a member of `fin (succ n)` -/
--   fs {n} : PFin2 n → PFin2 (succ n)
--   deriving DecidableEq
--
-- namespace PFin2
--
-- /-- Ex falso. The dependent eliminator for the empty `PFin2 0` type. -/
-- def elim0 {C : PFin2 0 → Sort u} : ∀ i : PFin2 0, C i :=
--   by intro i; cases i
--
-- /-- Converts a `PFin2` into a natural. -/
-- def toNat : ∀ {n}, PFin2 n → Nat
--   | _, @fz _ => 0
--   | _, @fs _ i => succ (toNat i)
--
-- /-- Shows that `toNat` produces a natural withing the range -/
-- theorem toNat_lt (i : PFin2 n) :
--   i.toNat < n :=
-- by
--   induction i
--   case fz       => apply succ_pos
--   case fs _ ih  => apply lt_succ_of_le ih
--
-- /-- Converts a `PFin2` into the a `Fin` -/
-- def toFin : PFin2 n → Fin n
--   := fun i => ⟨i.toNat, toNat_lt i⟩
--
-- /-- Converts a natural into a `PFin2` given a proof that it is in range -/
-- def ofNatLt : ∀ {n} (k : Nat) (_ : k < n), PFin2 n
--   | 0, _, h            => by contradiction
--   | succ n, 0, _       => fz
--   | succ n, succ k, h  => fs $ @ofNatLt n k (lt_of_succ_lt_succ h)
--
--
-- /-- Converts a `Fin` into a `PFin2` -/
-- def ofFin : Fin n → PFin2 n
--   := fun ⟨i, h⟩ => ofNatLt i h
--
--
--
-- /-- This is a simple type class inference prover for proof obligations
--   of the form `m < n` where `m n : Nat`. -/
-- class IsLt (m n : Nat) where
--   h : m < n
--
-- instance IsLt.zero n : IsLt 0 (succ n) :=
--   ⟨succ_pos _⟩
--
-- instance IsLt.succ m n [l : IsLt m n] : IsLt (succ m) (succ n) :=
--   ⟨succ_lt_succ l.h⟩
--
-- /-- Use type class inference to infer the boundedness proof, so that we can directly convert a
-- `nat` into a `PFin2 n`. This supports notation like `&1 : fin 3`. -/
-- def ofNat' : ∀ {n} m [IsLt m n], PFin2 n
--   | 0, _, ⟨h⟩ => absurd h (Nat.not_lt_zero _)
--   | succ _, 0, ⟨_⟩ => fz
--   | succ n, succ m, ⟨h⟩ => fs (@ofNat' n m ⟨lt_of_succ_lt_succ h⟩)
--
-- instance : Inhabited (PFin2 1) :=
--   ⟨fz⟩
--
--
-- /--
--   Weakens the bound on a `PFin2`, without changing the value
-- -/
-- def weaken : PFin2 n → PFin2 (succ n)
--   | fz   => fz
--   | fs k => fs $ weaken k
--
-- /--
--   The maximal element of `PFin2 (n+1)`, i.e., `n`
-- -/
-- def last : {n : Nat} → PFin2 (n+1)
--   | 0   => fz
--   | n+1 => fs (@last n)
--
-- /--
--   The inverse of `i` w.r.t. addition modulo `n`, i.e., .last - i
-- -/
-- def inv : {n : Nat} → PFin2.{u} n → PFin2.{u} n
--   | 0,    _     => by contradiction
--   | 1,    .fs _ => by contradiction
--   | n+1,  .fz   => last
--   | n+2,  .fs i => i.inv.weaken
--
-- theorem inv_last_eq_fz {n : Nat} :
--   (@last n).inv = .fz :=
-- by
--   induction n <;> simp [inv, last, weaken, *]
--
-- theorem inv_weaken_eq_fs_inv {n : Nat} (i : PFin2 n):
--   inv (weaken  i) = .fs (inv i) :=
-- by
--   induction i
--   <;> simp[inv, weaken, last]
--   case fs n i ih =>
--     simp[ih]
--     cases n
--     . contradiction
--     . simp[inv, weaken]
--
--
-- @[simp]
-- theorem inv_involution {i : PFin2 n} :
--   i.inv.inv = i :=
-- by
--     induction i
--     simp [inv]
--     case fz => apply inv_last_eq_fz
--     case fs n i ih => {
--       cases n;
--       case zero => contradiction
--       case succ n =>
--         simp[inv]
--         rw[inv_weaken_eq_fs_inv i.inv]
--         apply congrArg
--         apply ih
--     }
--
--
--     -- case zero.fs => contradiction
--     -- case succ.fs => simp[inv_last_eq_fz, weaken]
--
--
-- /--
--   Typeclass instances to make it easier to work with `PFin2`'s
-- -/
-- @[simp]
-- instance (n : Nat) : OfNat (PFin2 (n+1)) (nat_lit 0) := ⟨fz⟩
-- instance (n : Nat) : OfNat (PFin2 (n+2)) (nat_lit 1) := ⟨fs 0⟩
-- instance (n : Nat) : OfNat (PFin2 (n+3)) (nat_lit 2) := ⟨fs 1⟩
--
-- def ofFin2 : Fin2 n → PFin2 n
--   | .fz   => .fz
--   | .fs i => .fs <| ofFin2 i
--
-- def toFin2 : PFin2 n → Fin2 n
--   | .fz   => .fz
--   | .fs i => .fs <| toFin2 i
--
-- @[simp]
-- theorem ofFin2_toFin2_iso {i : Fin2 n} :
--   (toFin2 <| ofFin2 i) = i :=
-- by
--   induction i
--   . rfl
--   . simp [ofFin2, toFin2, *]
--
-- @[simp]
-- theorem toFin2_ofFin2_iso {i : PFin2 n} :
--   (ofFin2 <| toFin2 i) = i :=
-- by
--   induction i
--   . rfl
--   . simp [ofFin2, toFin2, *]
--
-- instance : Coe (Fin2 n) (PFin2 n) := ⟨ofFin2⟩
-- instance : Coe (PFin2 n) (Fin2 n) := ⟨toFin2⟩
--
-- instance : Coe (PFin2 n) (Fin n) := ⟨toFin⟩
-- instance : Coe (Fin n) (PFin2 n) := ⟨ofFin⟩
--
-- instance : Coe (Fin n) (Fin2 n) := ⟨fun i => toFin2 <| ofFin.{0} i⟩
-- instance : Coe (Fin2 n) (Fin n) := ⟨fun i => toFin <| ofFin2.{0} i⟩
--
-- end PFin2
--
--
namespace Fin2
  /--
  Typeclass instances to make it easier to work with `PFin2`'s
-/
@[simp]
instance (n : Nat) : OfNat (Fin2 (n+1)) (nat_lit 0) := ⟨fz⟩
instance (n : Nat) : OfNat (Fin2 (n+2)) (nat_lit 1) := ⟨fs 0⟩
instance (n : Nat) : OfNat (Fin2 (n+3)) (nat_lit 2) := ⟨fs 1⟩

-- def inv : Fin2 n → Fin2 n
--   := fun i => (PFin2.inv.{0} i : PFin2 n)

/--
  Weakens the bound on a `PFin2`, without changing the value
-/
def weaken : Fin2 n → Fin2 (succ n)
  | fz   => fz
  | fs k => fs $ weaken k

/--
  The maximal element of `PFin2 (n+1)`, i.e., `n`
-/
def last : {n : Nat} → Fin2 (n+1)
  | 0   => fz
  | n+1 => fs (@last n)

/--
  The inverse of `i` w.r.t. addition modulo `n`, i.e., .last - i
-/
def inv : {n : Nat} → Fin2 n → Fin2 n
  | 0,    _     => by contradiction
  | 1,    .fs _ => by contradiction
  | n+1,  .fz   => last
  | n+2,  .fs i => i.inv.weaken

theorem inv_last_eq_fz {n : Nat} :
  (@last n).inv = .fz :=
by
  induction n <;> simp [inv, last, weaken, *]

theorem inv_weaken_eq_fs_inv {n : Nat} (i : Fin2 n):
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
theorem inv_involution {i : Fin2 n} :
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

/-- Shows that `toNat` produces a natural withing the range -/
theorem toNat_lt (i : Fin2 n) :
  i.toNat < n :=
by
  induction i
  case fz       => apply succ_pos
  case fs _ ih  => apply lt_succ_of_le ih

/-- Converts a `PFin2` into the a `Fin` -/
def toFin : Fin2 n → Fin n
  := fun i => ⟨i.toNat, toNat_lt i⟩

/-- Converts a natural into a `PFin2` given a proof that it is in range -/
def ofNatLt : ∀ {n} (k : Nat) (_ : k < n), Fin2 n
  | 0, _, h            => by contradiction
  | succ n, 0, _       => fz
  | succ n, succ k, h  => fs $ @ofNatLt n k (lt_of_succ_lt_succ h)


/-- Converts a `Fin` into a `PFin2` -/
def ofFin : Fin n → Fin2 n
  := fun ⟨i, h⟩ => ofNatLt i h

instance : Coe (Fin n) (Fin2 n) := ⟨fun i => ofFin i⟩
instance : Coe (Fin2 n) (Fin n) := ⟨fun i => toFin i⟩

end Fin2
