/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
import Qpf.PFunctor.Multivariate.Basic 
import Qpf.PFunctor.Univariate.M
import Qpf.Mathlib
import Qpf.MathlibPort.Sigma

/-!
# The M construction as a multivariate polynomial functor.

M types are potentially infinite tree-like structures. They are defined
as the greatest fixpoint of a polynomial functor.

## Main definitions

 * `M.mk`     - constructor
 * `M.dest`   - destructor
 * `M.corec`  - corecursor: useful for formulating infinite, productive computations
 * `M.bisim`  - bisimulation: proof technique to show the equality of infinite objects

## Implementation notes

Dual view of M-types:

 * `Mp`: polynomial functor
 * `M`: greatest fixed point of a polynomial functor

Specifically, we define the polynomial functor `Mp` as:

 * A := a possibly infinite tree-like structure without information in the nodes
 * B := given the tree-like structure `t`, `B t` is a valid path
   from the root of `t` to any given node.

As a result `Mp.obj α` is made of a dataless tree and a function from
its valid paths to values of `α`

The difference with the polynomial functor of an initial algebra is
that `A` is a possibly infinite tree.

## Reference

 * Jeremy Avigad, Mario M. Carneiro and Simon Hudon.
   [*Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/


universe u

open_locale MvFunctor

namespace MvPFunctor

open TypeVec

variable {n : Nat} (P : MvPFunctor.{u} (n + 1))

/-- A path from the root of a tree to one of its node -/
inductive M.Path : P.last.M → Fin2 n → Type u
  | root (x : P.last.M) 
         (a : P.A) 
         (f : P.last.B a → P.last.M) 
         (h : PFunctor.M.dest x = ⟨a, f⟩) 
         (i : Fin2 n)
         (c : P.drop.B a i) : Path x i
  | child (x : P.last.M) (a : P.A) (f : P.last.B a → P.last.M) (h : PFunctor.M.dest x = ⟨a, f⟩) 
      (j : P.last.B a)
      (i : Fin2 n) (c : Path (f j) i) : Path x i

instance M.Path.inhabited (x : P.last.M) {i} [Inhabited (P.drop.B x.head i)] : 
  Inhabited (M.Path P x i) 
:=  let a := PFunctor.M.head x
    let f := PFunctor.M.children x
    ⟨M.Path.root 
      x _ a f
      (PFunctor.M.casesOn'
        (r:=fun _ => PFunctor.M.dest x = ⟨a, f⟩) 
        x 
        <| by
            intros a f
            simp [PFunctor.M.dest_mk, PFunctor.M.dest]
        )
      default⟩

/-- Polynomial functor of the M-type of `P`. `A` is a data-less
possibly infinite tree whereas, for a given `a : A`, `B a` is a valid
path in tree `a` so that `Wp.obj α` is made of a tree and a function
from its valid paths to the values it contains -/
def Mp : MvPFunctor n where
  A := P.last.M
  B := M.Path P

/-- `n`-ary M-type for `P` -/
def M (α : TypeVec n) : Type _ :=
  P.Mp.Obj α

instance mvfunctorM : MvFunctor P.M := by
  delta M <;> infer_instance

instance inhabitedM {α : TypeVec _} [I : Inhabited P.A] [∀ i : Fin2 n, Inhabited (α i)] : Inhabited (P.M α) :=
  @Obj.inhabited _ (Mp P) _ (@PFunctor.M.inhabited P.last I) _

/-- construct through corecursion the shape of an M-type
without its contents -/
def M.corecShape {β : Type u} (g₀ : β → P.A) (g₂ : ∀ b : β, P.last.B (g₀ b) → β) : β → P.last.M :=
  PFunctor.M.corec fun b => ⟨g₀ b, g₂ b⟩

/-- Proof of type equality as an arrow -/
def castDropB {a a' : P.A} (h : a = a') : P.drop.B a ⟹ P.drop.B a' 
  := fun i b => Eq.recOn (motive:=fun a' _ => B (drop P) a' i) h b

/-- Proof of type equality as a function -/
def castLastB {a a' : P.A} (h : a = a') : P.last.B a → P.last.B a' 
  := fun b => Eq.recOn (motive:=fun a' _ => PFunctor.B (last P) a') h b

/-- Using corecursion, construct the contents of an M-type -/
def M.corecContents {α : TypeVec.{u} n} {β : Type u} 
                    (g₀ : β → P.A) 
                    (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α)
                    (g₂ : ∀ b : β, P.last.B (g₀ b) → β)
                    (x : _)
                    (b : β)
                    (h: x = M.corecShape P g₀ g₂ b)
                  : M.Path P x ⟹ α
  | _, M.Path.root _ i a f h' c =>
    have : a = g₀ b := by
      rw [h, M.corecShape, PFunctor.M.dest_corec] at h'
      cases h'
      rfl
    g₁ b i (P.castDropB this i c)
  | _, M.Path.child _ i a f h' j c =>
    have h₀ : a = g₀ b := by
      rw [h, M.corecShape, PFunctor.M.dest_corec] at h'
      cases h'
      rfl
    have h₁ : f j = M.corecShape P g₀ g₂ (g₂ b (castLastB P h₀ j)) := by
      rw [h, M.corecShape, PFunctor.M.dest_corec] at h'
      cases h'
      rfl
    corecContents g₀ g₁ g₂ (f j) (g₂ b (P.castLastB h₀ j)) h₁ i c

/-- Corecursor for M-type of `P` -/
def M.corec' {α : TypeVec n} {β : Type u} (g₀ : β → P.A) (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : ∀ b : β, P.last.B (g₀ b) → β) : β → P.M α := fun b =>
  ⟨M.corecShape P g₀ g₂ b, M.corecContents P g₀ g₁ g₂ _ _ rfl⟩

/-- Corecursor for M-type of `P` -/
def M.corec {α : TypeVec n} {β : Type u} (g : β → P.Obj (α.append1 β)) : β → P.M α :=
  M.corec' P (fun b => (g b).fst) (fun b => dropFun (g b).snd) fun b => lastFun (g b).snd

/-- Implementation of destructor for M-type of `P` -/
def M.pathDestLeft {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M} (h : PFunctor.M.dest x = ⟨a, f⟩)
    (f' : M.Path P x ⟹ α) : P.drop.B a ⟹ α := fun i c => f' i (M.Path.root x i a f h c)

/-- Implementation of destructor for M-type of `P` -/
def M.pathDestRight {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M}
    (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) : ∀ j : P.last.B a, M.Path P (f j) ⟹ α := fun j i c =>
  f' i (M.Path.child x i a f h j c)

/-- Destructor for M-type of `P` -/
def M.dest' {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M} (h : PFunctor.M.dest x = ⟨a, f⟩)
    (f' : M.Path P x ⟹ α) : P.Obj (α.append1 (P.M α)) :=
  ⟨a, splitFun (M.pathDestLeft P h f') fun x => ⟨f x, M.pathDestRight P h f' x⟩⟩

/-- Destructor for M-types -/
def M.dest {α : TypeVec n} (x : P.M α) : P.Obj (α ::: P.M α) :=
  M.dest' P (Sigma.eta <| PFunctor.M.dest x.fst).symm x.snd

/-- Constructor for M-types -/
def M.mk {α : TypeVec n} : P.Obj (α.append1 (P.M α)) → P.M α :=
  M.corec _ fun i => appendFun id (M.dest P) <$$> i

theorem M.dest'_eq_dest'  {α : TypeVec n} 
                          {x : P.last.M} 
                          {a₁ : P.A} 
                          {f₁ : P.last.B a₁ → P.last.M}
                          (h₁ : PFunctor.M.dest x = ⟨a₁, f₁⟩)
                          {a₂ : P.A} 
                          {f₂ : P.last.B a₂ → P.last.M} 
                          (h₂ : PFunctor.M.dest x = ⟨a₂, f₂⟩)
                          (f' : M.Path P x ⟹ α) 
                    : M.dest' P h₁ f' = M.dest' P h₂ f' := by
  cases h₁.symm.trans h₂ <;> rfl

theorem M.dest_eq_dest' {α : TypeVec n} 
                        {x : P.last.M} 
                        {a : P.A} 
                        {f : P.last.B a → P.last.M}
                        (h : PFunctor.M.dest x = ⟨a, f⟩) 
                        (f' : M.Path P x ⟹ α) 
                    : M.dest P ⟨x, f'⟩ = M.dest' P h f' :=
  dest'_eq_dest' _ _ _ _

theorem M.dest_corec' {α : TypeVec.{u} n} {β : Type u} (g₀ : β → P.A) (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : ∀ b : β, P.last.B (g₀ b) → β) (x : β) :
    M.dest P (M.corec' P g₀ g₁ g₂ x) = ⟨g₀ x, splitFun (g₁ x) (M.corec' P g₀ g₁ g₂ ∘ g₂ x)⟩ :=
  rfl

theorem M.dest_corec {α : TypeVec n} {β : Type u} (g : β → P.Obj (α.append1 β)) (x : β) :
    M.dest P (M.corec P g x) = appendFun id (M.corec P g) <$$> g x := by
  apply Eq.trans
  apply M.dest_corec'
  have : (fun b => (g b).fst) x = (g x).fst := by rfl;
  simp [this]; clear this;

  cases' g x with a f;
  rw [MvPFunctor.map_eq];
  apply congrArg
  conv => rhs rw [← split_drop_fun_last_fun f, append_fun_comp_split_fun]

theorem Mp_A_unfold : (Mp P).A = PFunctor.M (last P) := by rfl

theorem M.bisim_lemma {α : TypeVec n} 
                      {a₁ : (Mp P).A} 
                      {f₁ : (Mp P).B a₁ ⟹ α} 
                      {a' : P.A} {f' : (P.B a').drop ⟹ α}
                      {f₁' : (P.B a').last → M P α} 
                      (e₁ : M.dest P ⟨a₁, f₁⟩ = ⟨a', splitFun f' f₁'⟩) 
                    :
    ∃ (g₁' : _) (e₁' : PFunctor.M.dest a₁ = ⟨a', g₁'⟩),
      f' = M.pathDestLeft P e₁' f₁ 
      ∧ f₁' = fun x : (last P).B a' => ⟨g₁' x, M.pathDestRight P e₁' f₁ x⟩ 
:= by
  revert e₁
  generalize ef : @splitFun n _ (append1 α (M P α)) f' f₁' = ff ;
  intro e₁;
  let he₁' := PFunctor.M.dest a₁;
  rcases e₁' : he₁' with ⟨a₁', g₁'⟩;
  rw [M.dest_eq_dest' P e₁'] at e₁
  cases e₁
  exact ⟨_, e₁', split_fun_inj ef⟩


theorem M.bisim {α : TypeVec n} (R : P.M α → P.M α → Prop)
    (h :
      ∀ x y,
        R x y → ∃ a f f₁ f₂, M.dest P x = ⟨a, splitFun f f₁⟩ ∧ M.dest P y = ⟨a, splitFun f f₂⟩ ∧ ∀ i, R (f₁ i) (f₂ i))
    x y (r : R x y) : x = y := by
  cases' x with a₁ f₁
  cases' y with a₂ f₂
  simp [Mp]  at *
  have : a₁ = a₂ := by
    refine' PFunctor.M.bisim (fun a₁ a₂ => ∃ x y, R x y ∧ x.1 = a₁ ∧ y.1 = a₂) _ _ _ ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩
    rintro _ _ ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩
    rcases h _ _ r with ⟨a', f', f₁', e₁, f₂', e₂, h'⟩
    rcases M.bisim_lemma P e₁ with ⟨g₁', e₁', rfl, rfl⟩
    rcases M.bisim_lemma P e₂ with ⟨g₂', e₂', _, rfl⟩
    rw [e₁', e₂']
    exact ⟨_, _, _, rfl, rfl, fun b => ⟨_, _, h' b, rfl, rfl⟩⟩
  subst this
  apply congrArg
  funext i p;
  induction' p with x i a f h' c x a f h' i c p IH <;>
    try
      rcases h _ _ r with ⟨a', f', f₁', f₂', e₁, e₂, h''⟩
      rcases M.bisim_lemma P e₁ with ⟨g₁', e₁', rfl, rfl⟩
      rcases M.bisim_lemma P e₂ with ⟨g₂', e₂', e₃, rfl⟩
      cases h'.symm.trans e₁'
      cases h'.symm.trans e₂'
  · let f' := fun (c : B (drop P) a i) => f₁ i (Path.root x i a f h' c)
    let g' := fun (c : B (drop P) a i) => f₂ i (Path.root x i a f h' c)
    show f' c = g' c
    apply congrFun _ c
    sorry
    -- exact (congrFun (congrFun _ i) c : _)
  · sorry
    -- exact IH _ _ (h'' _)
    

theorem M.bisim₀ {α : TypeVec n} (R : P.M α → P.M α → Prop) (h₀ : Equivalence R)
    (h : ∀ x y, R x y → (id ::: Quot.mk R) <$$> M.dest _ x = (id ::: Quot.mk R) <$$> M.dest _ y) x y (r : R x y) :
    x = y := by
  apply M.bisim P R _ _ _ r
  clear r x y
  introv Hr
  specialize h _ _ Hr
  clear Hr
  let ax := (M.dest P x).1
  let fx := (M.dest P x).2
  have : M.dest P x = ⟨ax, fx⟩
    := by trivial
  rw [this] at h; clear this
  let ay := (M.dest P y).1
  let fy := (M.dest P y).2
  have : M.dest P y = ⟨ay, fy⟩
    := by trivial
  rw [this] at h; clear this
  rw [map_eq, map_eq] at h
  injection h with h₂ h₁
  rw [←h₂] at *
  clear h₂
  sorry
  /- FIXME
  simp only [heq_iff_eq] at h₁
  -- clear h
  have Hdrop : dropFun fx = dropFun fy := by
    replace h₁ := congr_argₓ dropFun h₁
    simpa using h₁
  exists ax, dropFun fx, lastFun fx, lastFun fy
  rw [split_drop_fun_last_fun, Hdrop, split_drop_fun_last_fun]
  simp
  intro i
  replace h₁ := congr_funₓ (congr_funₓ h₁ Fin2.fz) i
  simp [(· ⊚ ·), appendFun, splitFun] at h₁
  replace h₁ := Quot.exact _ h₁
  rw [h₀.eqv_gen_iff] at h₁
  exact h₁
  -/

theorem M.bisim' {α : TypeVec n} (R : P.M α → P.M α → Prop)
    (h : ∀ x y, R x y → (id ::: Quot.mk R) <$$> M.dest _ x = (id ::: Quot.mk R) <$$> M.dest _ y) x y (r : R x y) :
    x = y := 
by
  sorry
  /-
  have := M.bisim₀ P (EqvGen R) _ _
  · solve_by_elim [EqvGen.rel]
    
  · apply EqvGen.is_equivalence
    
  · clear r x y
    introv Hr
    have : ∀ x y, R x y → EqvGen R x y := @EqvGen.rel _ R
    induction Hr
    · rw [← Quot.factor_mk_eq R (EqvGen R) this]
      rwa [append_fun_comp_id, ← MvFunctor.map_map, ← MvFunctor.map_map, h]
      
    all_goals
      cc
  -/
    

theorem M.dest_map {α β : TypeVec n} (g : α ⟹ β) (x : P.M α) :
    M.dest P (g <$$> x) = (appendFun g fun x => g <$$> x) <$$> M.dest P x := by
  cases' x with a f
  rw [map_eq]
  conv => rhs rw [M.dest, M.dest', map_eq, append_fun_comp_split_fun]

theorem M.map_dest {α β : TypeVec n} (g : (α ::: P.M α) ⟹ (β ::: P.M β)) (x : P.M α)
    (h : ∀ x : P.M α, lastFun g x = (dropFun g <$$> x : P.M β)) : g <$$> M.dest P x = M.dest P (dropFun g <$$> x) := by
  rw [M.dest_map]
  apply congrFun;
  apply congrArg;
  apply eq_of_drop_last_eq <;> simp
  . intro; constructor;
  ext1
  apply h

end MvPFunctor

