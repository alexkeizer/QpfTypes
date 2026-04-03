/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon, Alex Keizer
-/
module

public import NewPFTypes.PFunctor.Multivariate.Basic
public import NewPFTypes.PFunctor.Univariate.M

/-!
# The M construction as a multivariate polynomial functor.

M types are potentially infinite tree-like structures. They are defined
as the greatest fixpoint of a polynomial functor.

## Main definitions

* `M.mk`     - constructor
* `M.dest`   - destructor
* `M.corec`  - corecursor: useful for formulating infinite, productive computations

## Implementation notes

Dual view of M-types:

* `mp`: polynomial functor
* `M`: greatest fixed point of a polynomial functor

Specifically, we define the polynomial functor `mp` as:

* A := a possibly infinite tree-like structure without information in the nodes
* B := given the tree-like structure `t`, `B t` is a valid path
  from the root of `t` to any given node.

As a result `mp α` is made of a dataless tree and a function from
its valid paths to values of `α`

The difference with the polynomial functor of an initial algebra is
that `A` is a possibly infinite tree.

## Reference

* Jeremy Avigad, Mario M. Carneiro and Simon Hudon.
  [*Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/
@[expose] public section

namespace QpfTypes
namespace MvPFunctor

open TypeVec

universe u

variable {n : Nat} (P : MvPFunctor.{u} (n + 1))

/-!
## Definition of the M Type
-/

/-- A path from the root of an M-type tree to one of its nodes -/
inductive M.Path : P.last.M → Fin n → Type u
  | root (x : P.last.M)
          (a : P.A)
          (f : P.last.B a → P.last.M)
          (h : PFunctor.M.dest x = ⟨a, f⟩)
          (i : Fin n)
          (c : P.drop.B a i) : M.Path x i
  | child (x : P.last.M)
          (a : P.A)
          (f : P.last.B a → P.last.M)
          (h : PFunctor.M.dest x = ⟨a, f⟩)
          (j : P.last.B a)
          (i : Fin n)
          (c : M.Path (f j) i) : M.Path x i

instance M.Path.inhabited (x : P.last.M) {i} [Inhabited (P.drop.B x.head i)] :
    Inhabited (M.Path P x i) :=
  let a := PFunctor.M.head x
  let f := PFunctor.M.children x
  ⟨M.Path.root _ a f rfl _ default⟩

/-- The polynomial functor underlying `P.M` -/
def mp : MvPFunctor n where
  A := P.last.M
  B := M.Path P

/-- `P.M α` is the M-type of `P`, parameterized by a TypeVec `α` -/
def M (α : TypeVec n) : Type _ := P.mp.Obj α

/-!
## API of the M Type
-/

instance inhabitedM {α : TypeVec _} [I : Inhabited P.A] [∀ i : Fin n, Inhabited (α i)] :
    Inhabited (P.M α) :=
  @MvPFunctor.Obj.inhabited _ (mp P) _ (@PFunctor.M.inhabited P.last I) _

/-! ### Corecursor -/

/-- Compute the shape (the underlying M-type of `P.last`) for a corecursive definition -/
def M.corecShape {β : Type u} (g₀ : β → P.A) (g₂ : ∀ b : β, P.last.B (g₀ b) → β) :
    β → P.last.M :=
  PFunctor.M.corec fun b => ⟨g₀ b, g₂ b⟩

/-- Cast drop-branch indices along a proof that two shapes are equal -/
def castDropB {a a' : P.A} (h : a = a') : P.drop.B a ⟹ P.drop.B a' :=
  fun _i b => h ▸ b

/-- Cast last-branch indices along a proof that two shapes are equal -/
def castLastB {a a' : P.A} (h : a = a') : P.last.B a → P.last.B a' :=
  fun b => h ▸ b

/-- Fill in the content (the path function) for a corecursive definition -/
def M.corecContents {α : TypeVec.{u} n} {β : Type u}
    (g₀ : β → P.A) (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : ∀ b : β, P.last.B (g₀ b) → β)
    (x : _) (b : β) (h : x = M.corecShape P g₀ g₂ b) : M.Path P x ⟹ α
  | _, M.Path.root x a f h' i c =>
    have ha : a = g₀ b := by
      rw [h, M.corecShape, PFunctor.M.dest_corec] at h'; cases h'; rfl
    g₁ b i (P.castDropB ha i c)
  | _, M.Path.child x a f h' j i c =>
    have h₀ : a = g₀ b := by
      rw [h, M.corecShape, PFunctor.M.dest_corec] at h'; cases h'; rfl
    have h₁ : f j = M.corecShape P g₀ g₂ (g₂ b (P.castLastB h₀ j)) := by
      rw [h, M.corecShape, PFunctor.M.dest_corec] at h'; cases h'; rfl
    M.corecContents g₀ g₁ g₂ (f j) (g₂ b (P.castLastB h₀ j)) h₁ i c

/-- The corecursor for `P.M` (general form with explicit components) -/
def M.corec' {α : TypeVec n} {β : Type u}
    (g₀ : β → P.A) (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : ∀ b : β, P.last.B (g₀ b) → β) : β → P.M α := fun b =>
  ⟨M.corecShape P g₀ g₂ b, M.corecContents P g₀ g₁ g₂ _ _ rfl⟩

/-- The corecursor for `P.M` -/
def M.corec {α : TypeVec n} {β : Type u} (g : β → P (α.append1 β)) : β → P.M α :=
  M.corec' P (fun b => (g b).fst) (fun b => dropFun (g b).snd) fun b => lastFun (g b).snd

/-- Left component of the destructor for paths -/
def M.pathDestLeft {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M}
    (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) : P.drop.B a ⟹ α :=
  fun i c => f' i (M.Path.root x a f h i c)

/-- Right component of the destructor for paths -/
def M.pathDestRight {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M}
    (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) :
    ∀ j : P.last.B a, M.Path P (f j) ⟹ α :=
  fun j i c => f' i (M.Path.child x a f h j i c)

/-! ### Destructor -/

/-- Destructor for `P.M`, given an explicit decomposition -/
def M.dest' {α : TypeVec n} {x : P.last.M} {a : P.A} {f : P.last.B a → P.last.M}
    (h : PFunctor.M.dest x = ⟨a, f⟩) (f' : M.Path P x ⟹ α) : P (α.append1 (P.M α)) :=
  ⟨a, splitFun (M.pathDestLeft P h f') fun x => ⟨f x, M.pathDestRight P h f' x⟩⟩

/-- Destructor for `P.M` -/
def M.dest {α : TypeVec n} (x : P.M α) : P (α ::: P.M α) :=
  let a := x.fst.head
  let f := x.fst.children
  M.dest' P (a:=a) (f:=f) (by rfl) x.snd

/-! ### Constructor -/

/-- Constructor for `P.M` -/
def M.mk {α : TypeVec n} : P (α.append1 (P.M α)) → P.M α :=
  M.corec P fun i => P.map (appendFun TypeVec.id (M.dest P)) i

/-!
## Additional Lemmas
-/

theorem M.dest'_eq_dest' {α : TypeVec n} {x : P.last.M} {a₁ : P.A}
    {f₁ : P.last.B a₁ → P.last.M} (h₁ : PFunctor.M.dest x = ⟨a₁, f₁⟩) {a₂ : P.A}
    {f₂ : P.last.B a₂ → P.last.M} (h₂ : PFunctor.M.dest x = ⟨a₂, f₂⟩)
    (f' : M.Path P x ⟹ α) :
    M.dest' P h₁ f' = M.dest' P h₂ f' := by
  cases h₁.symm.trans h₂; rfl

theorem M.dest_eq_dest' {α : TypeVec n} {x : P.last.M} {a : P.A}
    {f : P.last.B a → P.last.M} (h : PFunctor.M.dest x = ⟨a, f⟩)
    (f' : M.Path P x ⟹ α) : M.dest P ⟨x, f'⟩ = M.dest' P h f' :=
  M.dest'_eq_dest' P _ _ _

theorem M.dest_corec' {α : TypeVec.{u} n} {β : Type u}
    (g₀ : β → P.A) (g₁ : ∀ b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : ∀ b : β, P.last.B (g₀ b) → β) (x : β) :
    M.dest P (M.corec' P g₀ g₁ g₂ x) =
    ⟨g₀ x, splitFun (g₁ x) (M.corec' P g₀ g₁ g₂ ∘ g₂ x)⟩ :=
  rfl

theorem M.dest_corec {α : TypeVec n} {β : Type u}
    (g : β → P (α.append1 β)) (x : β) :
    M.dest P (M.corec P g x) = P.map (appendFun TypeVec.id (M.corec P g)) (g x) := by
  rw [corec, M.dest_corec']
  obtain ⟨a, f⟩ := g x
  simp only [MvPFunctor.map_eq]
  congr 1
  rw [← split_dropFun_lastFun f, appendFun_comp_splitFun]
  rfl


end MvPFunctor
end QpfTypes
