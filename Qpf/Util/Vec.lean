/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon, Alex Keizer
-/

import Qpf.MathlibPort.Fin2
import Qpf.Util.HEq
import Lean.Elab.Tactic.Conv

universe u v w

inductive Vec (α : Type _) : Nat → Type _ where
  | nil : Vec α 0
  | append1 (tl : Vec α n) (hd : α) : Vec α (n+1)

/--
n-tuples of types, as a category
-/
def TypeVec := Vec (Type _)

inductive DVec : TypeVec n → Type _ where
  | nil     : DVec (Vec.nil)
  | append1 {αs : Vec (Type _) n} (tl : DVec αs) (hd : α) : DVec (Vec.append1 αs α)

namespace Vec
  /-- Return the last element from a `Vec` -/
  abbrev last : Vec α (n+1) → α
  | append1 _ hd => hd

  /-- Drop the last element from a `Vec` -/
  def drop : Vec α (n+1) → Vec α n
  | append1 tl _ => tl

  def constVec {α : Type _} (a : α) : (n : Nat) → Vec α n
  | 0   => nil
  | n+1 => append1 (constVec a n) a
end Vec

-- unif_hint (n : Nat) where |- Fin2 n → Type u =?= Vec (Type u) n
-- unif_hint {α : Type _} (n : Nat) where |- DVec (Vec.constVec α n) =?= Vec α n

namespace DVec
  /-- Return the last element from a `DVec` -/
  abbrev last : DVec (.append1 αs α) → α
  | append1 _ hd => hd

  /-- Drop the last element from a `DVec` -/
  def drop : DVec (.append1 αs α) → DVec αs
  | append1 tl _ => tl

  -- infixl:67 " ::: " => append1
end DVec



/-
  # Notation macros
-/

syntax "![" term,* "]" : term
macro_rules
  | `(![])    => `(Vec.nil)
  | `(![$x])  => `(Vec.append1 ![] $x)
  | `(![ $xs,* , $x]) => `(Vec.append1 ![$xs,*] $x)



namespace Vec
  theorem drop_append1 {v : Vec α n} {a : α} : 
      drop (append1 v a) = v :=
  by rfl

  theorem last_append1 {v : Vec α n} {a : α} : 
    last (append1 v a) = a
  := rfl

  @[simp]
  theorem append1_drop_last (v : Vec α (n+1)) : 
    append1 (drop v) (last v) = v :=
  by
    cases v; rfl

  def prepend1 (a : α) : Vec α n → Vec α (n+1)
  | nil           => append1 nil a
  | append1 tl hd => append1 (prepend1 a tl) hd

  def reverse : Vec α n → Vec α n
  | nil           => nil
  | append1 tl hd => prepend1 hd (reverse tl)


  theorem reverse_prepend1_eq_append1 :
    reverse (prepend1 hd tl) = append1 (reverse tl) hd :=
  by
    induction tl
    . rfl
    . simp[reverse, prepend1, *]

  @[simp]
  theorem reverse_involution {v : Vec α n} :
    v.reverse.reverse = v :=
  by
    induction v
    . rfl
    . simp[reverse, reverse_prepend1_eq_append1, *]


  def default [i : Inhabited α] : (n : Nat) → Vec α n
  | 0   => nil
  | n+1 => append1 (default n) i.default

  instance instInhabited [Inhabited α] : 
    Inhabited (Vec α n) := 
  ⟨default n⟩


  def get : Vec α n → Fin2 n → α 
  | nil,          i     => by contradiction
  | append1 _ hd, .fz   => hd
  | append1 tl _, .fs i => tl.get i

  /-
    The following is invoked whenever `v[i]` is used
  -/
  def getOp (self : Vec α n) (idx : Fin2 n) : α 
    := self.get idx


  /--
    Construct a `Vec` from a function `f : Fin2 n → α`
  -/
  def ofFn : {n : Nat} → (Fin2 n → α) → Vec α n 
  | 0,    _ => Vec.nil
  | n+1,  f => Vec.append1 (ofFn fun i => f i.fs) (f 0)


  #check List.map

  /--
    Map a function over the vec
  -/
  def map (f : α → β) : Vec α n → Vec β n
  | .nil            => .nil
  | .append1 tl hd  => .append1 (tl.map f) (f hd)


  def zip : Vec α n → Vec β n → Vec (α × β) n
  | .nil,             .nil              => .nil
  | .append1 tl₁ hd₁, .append1 tl₂ hd₂  => .append1 (tl₁.zip tl₂) (hd₁, hd₂)
  

  def mapD  {α : Type _} {β : α → Type _} 
            (f : (a : α) → β a) : (v : Vec α n) → DVec (v.map β)
  | .nil            => .nil
  | .append1 tl hd  => .append1 (tl.mapD f) (f hd)

end Vec