import Mathlib.Control.Functor.Multivariate
import Mathlib.Data.PFunctor.Multivariate.Basic
import Mathlib.Data.PFunctor.Multivariate.M
import Mathlib.Data.QPF.Multivariate.Basic

import Qpf.Qpf.Multivariate.Constructions.Cofix
import Qpf.Util


open TypeVec MvFunctor

namespace MvQPF
  variable {n : Nat} (P : MvPFunctor.{u} (n+1))

  /--
    A `P`-coalgebra is a state machine.

    We carefully construct it so that the `Coalgebra` type lives in `Type u + 1`,
    which is also the universe of arguments to `P.Obj`.
    This allows us to construct the final coalgebra as a quotient of `Coalgebra`
  -/
  structure Coalgebra (α : TypeVec n) where
    /-- States of the coalgebra -/
    σ : Type u
    /-- Single step unfold -/
    unfold : σ → P.Obj (α ::: σ)

  /--
    A *pointed* `P`-coalgebra is a state machine plus an initial state
  -/
  structure PointedCoalgebra (α : TypeVec n) extends Coalgebra P α where
    /-- The current state -/
    point : σ 
  
  
  namespace PointedCoalgebra
    variable {P} {α : TypeVec n}

    -- /--
    --   We can view a `PointedCoalgebra` as a state in the Coalgebra of Coalgebras.
    --   This function is the `unfold` operation for this Coalgebra of Coalgebras
    -- -/
    -- def unfoldRoot (c : PointedCoalgebra P α) : P.Obj (α ::: PointedCoalgebra P α) :=
    --   (id ::: (fun d => ⟨c.toCoalgebra, d.down⟩)) <$$> (c.unfold c.point)

    def bisimilar (c₁ c₂ : PointedCoalgebra P α) : Prop :=
      ∃ (R : c₁.σ → c₂.σ → Prop), 
        R c₁.point c₂.point
        ∧ ∀ {s₁ s₂}, R s₁ s₂ → 
          let ⟨a₁, f₁⟩ := c₁.unfold s₁
          let ⟨a₂, f₂⟩ := c₂.unfold s₂
          ∃ (h : a₁ = a₂), 
            (∀ b, R (f₁ 0 b) (f₂ 0 <| cast (by rw[h]) b))
            ∧ (∀ i b, (f₁ (Fin2.fs i) b) = (f₂ (Fin2.fs i) <| cast (by rw[h]) b))

    

    def bisimilar.iseqv : Equivalence (@bisimilar n P α) where
      refl  := 
        by
          intro c
          use fun x y => x = y
          apply And.intro
          . rfl
          . intro s₁ s₂ eq
            cases eq
            cases c.unfold s₁
            simp
      symm  :=
        by
          intro c₁ c₂ ⟨R, hpoint, h⟩
          use fun x y => R y x
          apply And.intro
          . assumption
          . intro s₂ s₁ rel
            specialize h rel
            revert h
            cases c₁.unfold s₁
            cases c₂.unfold s₂
            simp only [forall_exists_index]
            rintro ⟨⟩ ⟨hr, heq⟩
            use rfl
            apply And.intro
            . intro b
              apply hr
            . intro i b
              apply Eq.symm
              apply heq
          
      trans :=
        by
          intro c₁ c₂ c₃ ⟨R₁, hpoint₁, h₁⟩ ⟨R₂, hpoint₂, h₂⟩
          use fun x z => ∃y, R₁ x y ∧ R₂ y z
          apply And.intro
          . use c₂.point
            exact And.intro hpoint₁ hpoint₂
          . intro s₁ s₃
            rintro ⟨s₂, ⟨hR₁, hR₂⟩⟩
            specialize h₁ hR₁
            specialize h₂ hR₂
            revert h₁ h₂
            rcases c₁.unfold s₁ with ⟨a₁, f₁⟩
            rcases c₂.unfold s₂ with ⟨a₂, f₂⟩
            rcases c₃.unfold s₃ with ⟨a₃, f₃⟩
            simp only [forall_exists_index]
            rintro ⟨⟩ ⟨hr₁, heq₁⟩ ⟨⟩ ⟨hr₃, heq₃⟩
            use rfl
            apply And.intro
            . intro b
              exact ⟨(f₂ 0 b), hr₁ b, hr₃ b⟩
            . intro i b
              apply Eq.trans (heq₁ i b) (heq₃ i b)

    def bisimilar.setoid : Setoid (PointedCoalgebra P α)  where
      r := (@bisimilar n P α)
      iseqv := iseqv
  end PointedCoalgebra



  /--
    States of the final coalgebra are equivalence classes of bisimilar, pointed coalgebras
  -/
  def FinalCoalgebra (α : TypeVec n) : Type (u + 1)
    := Quotient (@PointedCoalgebra.bisimilar.setoid n P α) 

  namespace FinalCoalgebra
    variable {P}

    def mk : PointedCoalgebra P α  → FinalCoalgebra P α 
      := Quotient.mk _

    def unfold : FinalCoalgebra P α → P.Obj (α ::: (FinalCoalgebra P α)) :=
      Quotient.lift 
        (fun c => (id ::: mk) <$$> c.unfoldRoot)
        (by 
          intro a b (eqv : a.bisimilar b)
          rcases eqv with ⟨R, points_related, is_bisim⟩
          rcases a with ⟨⟨σ₁, unfold₁⟩, p₁⟩
          rcases b with ⟨⟨σ₂, unfold₂⟩, p₂⟩

          have := is_bisim points_related
          revert this

          simp only [PointedCoalgebra.unfoldRoot]
          rcases unfold₁ p₁ with ⟨a₁, f₁⟩
          rcases unfold₂ p₂ with ⟨a₂, f₂⟩
          simp only [MvFunctor.map, MvPFunctor.map, mk, comp]

          rintro ⟨⟨⟩, hrel, heq⟩
          congr
          funext i x
          cases i <;> simp only [appendFun, splitFun]
          . apply Quotient.sound
            use R
            apply And.intro
            . apply hrel
            . assumption
          . apply heq
          

        )

  end FinalCoalgebra


  namespace Coalgebra
    /-- We can view the type of possibly infinite trees as a coalgebra -/
    def ofM : Coalgebra P α where 
      σ := P.M α
      unfold := _

  end Coalgebra

  namespace PointedCoalgebra
    /--
      Produce the full, non-wellfounded tree that is generated by this coalgebra
    -/
    def generate (c : PointedCoalgebra P α) : P.M α :=
      .corec P (fun s => c.unfold s.down) (ULift.up c.point)

    
    def ofM (c : P.M α) : PointedCoalgebra P α where
      σ := P.M α


  end PointedCoalgebra


  namespace FinalCoalgebra

    def generate (c : FinalCoalgebra P α) : P.M α :=
      .corec P FinalCoalgebra.unfold c

  end FinalCoalgebra

end MvQPF