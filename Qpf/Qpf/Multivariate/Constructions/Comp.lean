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
      simp only [(· <$$> ·), MvPFunctor.map, comp.mk, comp.get, TypeVec.comp]
      congr 2
      {
        funext i b
        rw[(p' i).repr_abs]
      }
      {
        apply HEq.funext
        . simp only [IsPolynomial.repr_abs]; rfl
        intro i

        have type_eq_α : B (comp (P F) fun i => P (G i))
            { fst := a',
              snd := fun x a =>
                (repr (abs { fst := f' x a, snd := fun j b => f j { fst := x, snd := { fst := a, snd := b } } })).fst }
            i =
          B (P (Comp F G)) { fst := a', snd := f' } i := 
          by simp only [IsPolynomial.repr_abs]; rfl
        
        apply HEq.funext'
        case type_eq_β => 
          intros; rfl
        case type_eq_α => 
          exact type_eq_α

        rintro ⟨b, ⟨b', g'⟩⟩
        simp only [heq_eq_eq]
        
        have : repr (abs 
                  ⟨ f' b b', 
                    fun j b_1 => 
                      f j ⟨b, ⟨b', b_1⟩⟩
                  ⟩)
                = ⟨ f' b b', 
                    fun j b_1 => 
                      f j ⟨b, ⟨b', b_1⟩⟩
                  ⟩;
        {
          simp [IsPolynomial.repr_abs]
        }
        simp[type_eq_α, this]
        /-
          TODO: properly finish this proof
        -/
        sorry
      }

    
    
    


end MvQPF.Comp

