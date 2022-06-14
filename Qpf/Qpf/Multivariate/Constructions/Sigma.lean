/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Qpf.PFunctor.Multivariate.Basic
import Qpf.Qpf.Multivariate.Basic

/-!
# Dependent product and sum of QPFs are QPFs
-/


universe u

namespace MvQpf

-- open_locale MvFunctor

variable {n : ℕ} {A : Type u}

variable (F : A → TypeFun.{u,u} n)

/-- Dependent sum of of an `n`-ary functor. The sum can range over
data types like `ℕ` or over `Type.{u-1}` -/
def Sigma (v : TypeVec.{u} n) : Type u :=
  _root_.Sigma fun (α : A) => F α v

/-- Dependent product of of an `n`-ary functor. The sum can range over
data types like `ℕ` or over `Type.{u-1}` -/
def Pi (v : TypeVec.{u} n) : Type u :=
  ∀ α : A, F α v

instance Sigma.inhabited {α} [Inhabited A] [Inhabited (F default α)] : Inhabited (Sigma F α) :=
  ⟨⟨default, default⟩⟩

instance Pi.inhabited {α} [∀ a, Inhabited (F a α)] : Inhabited (Pi F α) :=
  ⟨fun a => default⟩

variable [∀ α, MvFunctor <| F α]

namespace Sigma

instance : MvFunctor (Sigma F) where
  map := @fun α β f ⟨a, x⟩ => ⟨a, f <$$> x⟩

variable [∀ α, MvQpf <| F α]

/-- polynomial functor representation of a dependent sum -/
protected def P : MvPFunctor n :=
  ⟨ _root_.Sigma fun a => (P (F a)).A, 
    fun x => (P (F x.1)).B x.2
  ⟩

/-- abstraction function for dependent sums -/
protected def abs ⦃α⦄ : (Sigma.P F).Obj α → Sigma F α
  | ⟨a, f⟩ => ⟨a.1, MvQpf.abs ⟨a.2, f⟩⟩

/-- representation function for dependent sums -/
protected def repr ⦃α⦄ : Sigma F α → (Sigma.P F).Obj α
  | ⟨a, f⟩ =>
    let x := MvQpf.repr f
    ⟨⟨a, x.1⟩, x.2⟩

instance : MvQpf (Sigma F) where
  P := Sigma.P F
  abs := fun {α} => Sigma.abs (α:=α) F
  repr := fun {α} => Sigma.repr (α:=α) F
  abs_repr := by
    rintro α ⟨x, f⟩
    have : { fst := (repr f).fst, snd := (repr f).snd } = repr f
      := by cases (repr f); rfl;
    simp [Sigma.repr, Sigma.abs, abs_repr, this]
  abs_map := 
    by
      rintro α β f ⟨x, g⟩
      simp [Sigma.abs, MvPFunctor.map_eq] 
      simp [(· <$$> ·), ← abs_map, ← MvPFunctor.map_eq]

end Sigma

namespace Pi

instance : MvFunctor (Pi F) where
  map := @fun α β f x a => f <$$> x a

variable [instMvQpf : ∀ α, MvQpf <| F α]

/-- polynomial functor representation of a dependent product -/
protected def P : MvPFunctor n :=
  ⟨∀ a, (P (F a)).A, 
    @fun x i => _root_.Sigma fun (a : A) => (P (F a)).B (x a) i
  ⟩

/-- abstraction function for dependent products -/
protected def abs ⦃α⦄ : (Pi.P F).Obj α → Pi F α
  | ⟨a, f⟩ => fun x => MvQpf.abs ⟨a x, fun i y => f i ⟨_, y⟩⟩

/-- representation function for dependent products -/
protected def repr ⦃α⦄ : Pi F α → (Pi.P F).Obj α
  | f => ⟨fun a => (MvQpf.repr (f a)).1, fun i a => (@MvQpf.repr _ _ _ (instMvQpf _) _ (f _)).2 _ a.2⟩

instance : MvQpf (Pi F) where
  P := Pi.P F
  abs := fun {α} => Pi.abs (α:=α) F
  repr := fun {α} => Pi.repr (α:=α) F
  abs_repr := 
  by
    rintro α f
    ext x
    have : { fst := (repr (f x)).fst, snd := fun i y => Sigma.snd (repr (f x)) i y } = repr (f x)
      := by apply congrArg
            simp
    simp [Pi.repr, Pi.abs, abs_repr, this]
    
  abs_map := 
  by
    rintro α β f ⟨x, g⟩
    simp only [Pi.abs, MvPFunctor.map_eq]
    ext x
    simp only [(· <$$> ·)] 
    simp only [← abs_map, MvPFunctor.map_eq]
    rfl

end Pi

end MvQpf

