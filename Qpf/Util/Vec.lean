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
  def append1 {α : Type u} {n} (tl : Vec α n) (hd : α) : Vec α (.succ n)
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

  def reverse (v : Vec α n) : Vec α n :=
    fun i => v i.inv


  @[simp]
  theorem reverse_involution {v : Vec α n} :
    v.reverse.reverse = v :=
  by
    funext i;
    simp[reverse]
    apply congrArg;
    exact Fin2.inv_involution
end Vec



/-
  # Notation macros
-/

syntax "![" term,* "]" : term
macro_rules
  | `(![])    => `(Vec.nil)
  | `(![$x])  => `(Vec.append1 ![] $x)
  | `(![ $xs,* , $x]) => `(Vec.append1 ![$xs,*] $x)





-- #check Lean.Meta.getMVarDecl

-- section 
--   open Lean Tactic Elab.Tactic

-- def elabVecEqAux : TacticM Unit := do
--   evalTactic <|← `(tactic| sorry)


-- #check Lean.Expr.app

-- open Lean Meta Elab.Term Expr in
-- elab "vec_eq " a:term b:term : term => do
--   let α ← mkFreshTypeMVar
--   let n ← mkFreshExprMVar (mkConst ``Nat)

--   let vec_type := mkApp2 (mkConst ``Vec) n α

--   let a' ← elabTermEnsuringType a vec_type
--   let b' ← elabTermEnsuringType b vec_type

--   synthesizeSyntheticMVarsNoPostponing

--   let n' ← match ←getExprMVarAssignment? n.mvarId! with
--   | none    => throwError "Failed to assign a value to {n}"
--   | some n' => pure n'
  
--   match ← whnf n' with
--   | Expr.app (Expr.const (`Nat.cons) ..) .. => 
--       by sorry
--   | Expr.app (Expr.const (`Nat) ..) ..        => 
--       by sorry
--   | _                                       => throwErrow "Nat literal expected:\n\t{n}"
  
-- end