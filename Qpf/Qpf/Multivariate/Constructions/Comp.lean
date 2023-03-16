/-
Copyright (c) 2023 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Mathlib
import Qpf.Util

/-!
  Show that the composition of polynomial QPFs is itself a polynomial QPF
-/

universe u

-- section
--   open Lean Meta Elab Tactic

--   #check TacticM

-- elab "heq_of_eq" : tactic => do
--   let goal ← getMainGoal

--   goal.withContext do
--     let goalType ← goal.getType

--     let x₁ ← mkFreshMVarId
--     let x₂ ← mkFreshMVarId
--     let heq ← mkAppM ``HEq #[Expr.mvar x₁, Expr.mvar x₂]

--     if !(←isDefEq goalType heq) then
--       return

--     Term.synthesizeSyntheticMVarsNoPostponing

--     let type_eq ← mkFreshMVarId
--     let type₁ ← x₁.getType
--     let type₂ ← x₂.getType
--     type_eq.setType <|← mkAppM ``Eq #[type₁, type₂]


--     replaceMainGoal [type_eq, goal]

  

-- end

namespace MvQPF.Comp
  open MvPFunctor MvFunctor

variable {n m : ℕ} 
         (F : TypeFun n) 
         (G : Vec (TypeFun m) n)
         [p : IsPolynomial F]
         [p' : ∀ i, IsPolynomial <| G i]


  instance : IsPolynomial (Comp F G) where
    repr_abs := by
      intros α x;
      rcases x with ⟨⟨a', f'⟩, f⟩
      simp only [Comp.get, Comp.mk, Function.comp_apply, repr, abs, ← p.abs_map, p.repr_abs]
      simp [(· <$$> ·), MvPFunctor.map, comp.mk, comp.get, TypeVec.comp]
      congr 2
      {
        funext i b
        rw[(p' i).repr_abs]
      }
      {
        have eq₁ : 
          B (comp (P F) fun i => P (G i)) ⟨a', fun x a =>
                (repr (abs { fst := f' x a, snd := fun j b => f j { fst := x, snd := { fst := a, snd := b } } })).fst 
                ⟩
          =
          B (P (Comp F G)) ⟨a', f'⟩
         := by simp only [IsPolynomial.repr_abs]; rfl
        
        have eq₂ : 
            ((B (comp (P F) fun i => P (G i)) ⟨a', fun x a =>
                  (repr (abs { fst := f' x a, snd := fun j b => f j { fst := x, snd := { fst := a, snd := b } } })).fst 
                  ⟩
            ) ⟹ α) 
            =
            (B (P (Comp F G)) ⟨a', f'⟩ ⟹ α)
          := by rw[eq₁]
        
        apply HEq.funext
        . rw [eq₁]
        intro i

        have : ∀ (a : B (comp (P F) fun i => P (G i)) 
                ⟨a',  fun x a =>
                        (repr (abs { fst := f' x a, snd := fun j b => f j { fst := x, snd := { fst := a, snd := b } } })).fst ⟩ i), 
          HEq (Sigma.snd <| repr <| abs ⟨
              f' a.fst a.snd.fst, 
              fun j b => f j { fst := a.fst, snd := { fst := a.snd.fst, snd := b } } 
            ⟩)
            (fun j b => f j { fst := a.fst, snd := { fst := a.snd.fst, snd := b } })
          := by 
              intro a
              rw[IsPolynomial.repr_abs]
        
        
        -- apply HEq.symm
        apply HEq.funext' (type_eq_α := by rw[eq₁]) (type_eq_β := by intros; rfl)
        . intro x
          rcases x with ⟨j, ⟨x, g⟩⟩;
          simp
          have :  repr (abs ⟨f' j x, fun j_1 b => f j_1 ⟨j, ⟨x, b⟩⟩⟩)
                  =
                  ⟨f' j x, fun j_1 b => f j_1 ⟨j, ⟨x, b⟩⟩⟩
            := by rw[IsPolynomial.repr_abs]
          have : HEq (Sigma.snd (repr (abs ⟨f' j x, fun j_1 b => f j_1 ⟨j, ⟨x, b⟩⟩⟩)))
                     (fun j_1 b => f j_1 ⟨j, ⟨x, b⟩⟩)
            := by 
                conv => {
                  arg 1
                  tactic => 
                    cases [this]
                }
                
          
          

          apply hcongr;
          . sorry
          . apply heq_of_eq
            rw [cast_arg']
            rw [heq_cast_right]
            sorry
          . intros; rfl
          sorry


      }

    
    
    


end MvQPF.Comp

