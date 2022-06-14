/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon, Alex Keizer
-/

import Qpf.MathlibPort.Fin2
import Qpf.Util.HEq
import Lean.Elab.Tactic.Conv

universe u v w

abbrev DVec {n : Nat} (αs : Fin2 n → Type u)  : Type _
  := (i : Fin2 n) → αs i

abbrev Vec (α : Type _) (n : Nat)
  := @DVec n fun _ => α

namespace Vec
  def append1 {α : Type u} {n} (tl : Vec α n) (hd : α) : Vec α (n+1)
    | (Fin2.fs i) => tl i
    | Fin2.fz     => hd

  -- infixl:67 " ::: " => append1

  /-- Drop the last element from a `Vec` -/
  def drop (v : Vec α (n+1)) : Vec α n
    := fun i => v (Fin2.fs i)

  def constVec {α : Type _} (a : α) (n : Nat) : Vec α n
    := fun _ => a
end Vec

unif_hint (n : Nat) where |- Fin2 n → Type u =?= Vec (Type u) n
unif_hint {α : Type _} (n : Nat) where |- DVec (Vec.constVec α n) =?= Vec α n

namespace DVec
  /-- Return the last element from a `DVec` -/
  def last (v : @DVec (n+1) αs ) : αs 0
    := v 0

  /-- Drop the last element from a `DVec` -/
  def drop (v : DVec αs) : DVec (Vec.drop αs)
    := fun i => v (Fin2.fs i)

  @[reducible]
  def nil : @DVec 0 αs
    := fun emp => by contradiction

  @[reducible]
  def append1 {α : Type u} {αs : Vec (Type u) n} (tl : DVec αs) (hd : α) : DVec (Vec.append1 αs α)
    | (Fin2.fs i) => tl i
    | Fin2.fz     => hd
  

  -- infixl:67 " ::: " => append1
end DVec

namespace Vec
  variable {α : Type _} {n : Nat}

  abbrev nil  : Vec α 0           := DVec.nil
  abbrev last : Vec α n.succ → α  := DVec.last


  /-
  # TypeClasses on Vecs
  Since a `Vec` contains finitely many elements, statements of the form `∀i, Class (v i)`
  can be inferred with the typeclass inference machinery using induction on the length of `Vec`s
  -/
  section
    -- `Class` is intended to range over (unary) typeclasses, but there is nothing preventing
    -- users to instantiate it with non-typeclass functions
    -- variable {α : Type _}

    -- /-- `VecClassAux k Class v` means that all but the last `k` 
    --     elements of `v` implement `Class` -/
    -- class VecClassAux (k : Nat) (Class : α → Type) {n : Nat} (v : Vec α (n+k)) where
    --   inst : ∀i : Fin2 n, Class (v <| i.add k)

    -- /-- `VecClass Class v` means that all element of `v` implement `Class` -/
    -- abbrev VecClass (Class : α → Type) {n : Nat} (v : Vec α n)
    --   := @VecClassAux α 0 Class n v

    -- variable {Class : α → Type _}


    -- /-- Base case, all element of a en empty vec vacuosly implement every typeclass -/
    -- instance instVecNil {v : Fin2 k → α}  : 
    --   ∀ i : Fin2 0, Class (v <| i.add' k) := 
    -- by intro i; contradiction

    -- instance instVecNil {v : Fin2 k → α}  : 
    --   VecClass Class v := 
    -- by constructor; intro i; contradiction

    -- example (fF' : Vec (TypeVec.{u} 2 → Type u) 0) : 
    --   ∀i, MvFunctor (fF' i) := 
    -- by infer_instance

    -- Since `Class` might not be a typeclass, Lean will complain we're putting
    -- it in the `[...]` inference binder, the following option turns this warning off.
    -- If a user tries to instantiate this definition in the case that `Class` is *not*
    -- a typeclass, Lean will throw an `type class instance expected` error
    -- set_option checkBinderAnnotations false

    
    -- instance instVecAppend1 {n k : Nat} 
    --           {v : Fin2 n → α} 
    --           [succ: ∀ i : Fin2 n, Class (v <| Fin2.fs i)] 
    --           [zero: Class (v Fin2.fz)] : 
    --   ∀ i, Class (v i)
    -- | Fin2.fz   => zero
    -- | Fin2.fs i => succ i


    -- instance instVecAppend1 {n : Nat} (k : Nat := 0)
    --           {v : Fin2 (n + 1 + k) → α} 
    --           [succ: ∀ i : Fin2 n, Class (v <| (i.fs).add k)] 
    --           [zero: Class (v <| (@Fin2.fz n).add k)] : 
    --   ∀ i : Fin2 (n + 1) , Class (v <| i.add k)
    -- | Fin2.fz   => zero
    -- | Fin2.fs i => succ i
  end
end Vec