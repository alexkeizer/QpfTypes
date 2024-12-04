import Qpf
import Mathlib.Data.QPF.Multivariate.Constructions.Sigma

#check MvPFunctor

/-!
# Interaction Trees

We define interaction trees, a coinductive data-structure used for giving
semantics of side-effecting, possibly non-terminating, programs

[1] https://arxiv.org/abs/1906.00046
[2] https://github.com/DeepSpec/InteractionTrees
-/

set_option trace.QPF true
-- set_option diagnostics true

-- codata ITree (E : Type → Type) A where
-- | ret (r : A)
-- | tau (t : ITree E A)
-- | vis (_ : (Ans : Type) ×  (    E Ans) ×  (    Ans → ITree E A))
-- -- vis :   {Ans : Type} -> (e : E Ans) -> (k : Ans -> ITree E A)  -> ITree E A

section HeadChild
  inductive ITree.HeadT : Type 1
  | ret
  | tau
  | vis (Ans : Type)

  def ITree.ChildT : ITree.HeadT -> TypeVec.{1} 2
  | .ret     => ![PFin2.{1} 1, PFin2.{1} 0] -- One `A`, zero `ρ`
  | .tau     => ![PFin2.{1} 0, PFin2.{1} 1] -- Zero `A`, one `ρ` (remember, `ρ` intuitively means `ITree E A`)
  | .vis Ans => ![PFin2.{1} 0, ULift.{1, 0} Ans] -- Zero `A`, and... `Ans` many `ρ`... -- ! where do we get Ans from?

  abbrev ITree.P : MvPFunctor.{1} 2 := ⟨ITree.HeadT, ITree.ChildT⟩
  abbrev ITree.F : TypeVec.{1} 2 -> Type 1 := ITree.P.Obj

  def ITree.box   : F α → P.Obj α := sorry
  def ITree.unbox : P.Obj α → F α := sorry
  def ITree.box_unbox_id : (x : P.Obj α) -> box (unbox x) = x := sorry
  def ITree.unbox_box_id : (x : F α) -> unbox (box x) = x := sorry
  instance ITree.instMvQPF : MvQPF ITree.F := MvQPF.ofPolynomial P box unbox box_unbox_id unbox_box_id sorry

  def ITree_ugly := MvQPF.Cofix ITree.F -- you could do it this way, but it will be very unwieldy. Hence shape types.
end HeadChild

set_option pp.universes true

section ShapeBase
  inductive ITree.Shape (E : Type -> Type) (A : Type 1) (ρ : Type 1) (ν : Type 1) : Type 1
  | ret (r : A) : ITree.Shape E A ρ ν
  | tau (t : ρ) : ITree.Shape E A ρ ν
  | vis (e : ν) : ITree.Shape ..
  -- | vis : (Ans : Type) × E Ans × (Ans → ρ) -> ITree.Shape E A ρ

  -- qpf ITree.Base (E : Type -> Type) (A : Type) ρ := ITree.Shape E A ρ ((Ans : Type) × ULift.{1} (E Ans) × (Ans → ρ))
  -- ! If only we had this instance... life would be so easy
  -- instance {E : Type -> Type} : MvQPF (TypeFun.ofCurried (n := 1) (ITree.Shape E A)) := sorry
  -- def ITree' (E : Type -> Type) (A : Type 1) : TypeFun.{1} 0 :=
  --   MvQPF.Cofix (TypeFun.ofCurried <| ITree.Shape E A)

  /-- `qpf G (Ans : Type) (E : Type → Type) A ρ ν := E Ans × (Ans → ρ)`, but universe-polymorphic -/
  abbrev G.Uncurried (Ans : Type 0) (E : Type 0 → Type 0) : TypeFun.{1, 1} 2 :=
    MvQPF.Comp (n := 2) (m := 2) -- compose two 2-ary (A, ρ) functors `E Ans` and `Ans -> ρ`
      (TypeFun.ofCurried Prod.{1, 1})
      -- (MvQPF.Prod.Prod')
      (
        (Vec.append1 Vec.nil (MvQPF.Const 2 <| ULift (E Ans))).append1
        (MvQPF.Comp (n := 1) (m := 2)
          (TypeFun.ofCurried (MvQPF.Arrow Ans))
          (Vec.append1 Vec.nil (MvQPF.Prj 1))
        )
      )

  -- Ideally we'd do this directly, but the QPF meta code isn't there yet -- qpf G_vis (E : Type -> Type) A ρ ν := (Ans : Type) × (E Ans × (Ans -> ρ))
  abbrev G_vis.Uncurried (E : Type → Type) : TypeFun.{1,1} 2 :=
    MvQPF.Sigma.{1} fun (Ans : Type) => (G.Uncurried Ans E)
  qpf G_ret (E : Type -> Type) A ρ := A
  qpf G_tau (E : Type -> Type) A ρ := ρ

  set_option trace.Meta.synthInstance true

  #check MvQPF.Prod.instMvFunctorProd'
  instance : MvQPF (TypeFun.ofCurried (n := 2) @Prod.{u}) :=
    sorry

  instance (i : PFin2 1) : MvQPF (Vec.append1 Vec.nil (MvQPF.Prj (n:=2) 1) i) := sorry
  #synth ∀i : PFin2 1, MvQPF (Vec.append1 Vec.nil (MvQPF.Prj (n:=2) 1) i)
  instance {Ans} {E : Type -> Type} : MvQPF.{1, 1} (G.Uncurried Ans E) := inferInstance
  instance {Ans} {E : Type -> Type} : MvQPF.{1, 1} (G.Uncurried Ans E) := inferInstance
  instance {E : Type -> Type} : MvQPF.{1, 1} (G_vis.Uncurried E) := inferInstance

  abbrev ITree.ConstructorFs (E : Type -> Type) : Fin2 3 -> TypeVec 2 -> Type 1 :=
    ![G_ret.Uncurried E, G_tau.Uncurried E, G_vis.Uncurried E]

  abbrev ITree.Base.Uncurried  (E : Type -> Type) : TypeFun 2 :=
    MvQPF.Comp (TypeFun.ofCurried (n := 3) (ITree.Shape E)) (ITree.ConstructorFs E)

  -- def ITree.Base.Uncurried' (E : Type -> Type) : TypeFun 2 := fun v => ITree.Shape E (v 1) ((ITree.ConstructorFs E) 0 v) -- what am I even doing
  abbrev ITree.Base (E : Type -> Type) (A ρ : Type 1) : Type 1 :=
    MvQPF.Comp (TypeFun.ofCurried (n := 3) (ITree.Shape E)) (ITree.ConstructorFs E) ![A, ρ]

  instance {E : Type -> Type} : MvQPF.{1, 1} (ITree.Base.Uncurried E) := inferInstance

  def ITree.Uncurried (E : Type -> Type) :=
    MvQPF.Cofix (ITree.Base.Uncurried E)
end ShapeBase

instance {E : Type -> Type} : MvQPF (ITree.Base.Uncurried E) := sorry

def ITree.Uncurried (E : Type -> Type) := MvQPF.Cofix (ITree.Base.Uncurried E)
def ITree (E : Type -> Type) (A : Type 1) : Type 1 := MvQPF.Cofix (ITree.Base.Uncurried E) ![A, A] -- ! why two

#reduce (types := true) TypeVec.{1} 2

#check 1
