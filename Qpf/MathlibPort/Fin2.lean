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

end Fin2

