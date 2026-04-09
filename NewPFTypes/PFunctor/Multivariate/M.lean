/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon, Alex Keizer
-/
module

public import NewPFTypes.PFunctor.Multivariate.Basic

/-!
# The M Type of a Multivariate Polynomial Functor

M types are potentially infinite tree-like structures.
They are defined as the greatest fixpoint of a polynomial functor.


## Main definitions

* `M.mk`     - constructor
* `M.dest`   - destructor
* `M.corec`  - corecursor: useful for formulating infinite, productive computations

## Implementation notes

The `M` type is defined as a sequence of approximations,
similar to how Avigad et al describe the _univariate_ M type.
This deviates quite a bit from how the M type of a _multivariate_ functor is
constructed in Mathlib (which implements a the multivariate
construction described by Avigad et al. in that same paper).

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

namespace Approx

/--
`CofixA P α k` is a `k`-deep approximation of an M-type element.
Depth 0 carries no information. Depth `k+1` stores a tag `a : P.A`,
non-recursive content `f : P.drop.B a ⟹ α`, and a depth-`k` subtree per child.
-/
inductive CofixA (α : TypeVec.{u} n) : Nat → Type u
  | continue : CofixA α 0
  | intro {k} (a : P.A) (f : P.drop.B a ⟹ α) (g : P.last.B a → CofixA α k)
      : CofixA α (k + 1)

section Defs
variable {P}

instance {α : TypeVec n} : Subsingleton (CofixA P α 0) :=
  ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩

def head' {α : TypeVec n} {k} : CofixA P α (k + 1) → P.A
  | .intro a _ _ => a

def content' {α : TypeVec n} {k} : (x : CofixA P α (k + 1)) → P.drop.B (head' x) ⟹ α
  | .intro _ f _ => f

def children' {α : TypeVec n} {k} : (x : CofixA P α (k + 1)) → P.last.B (head' x) → CofixA P α k
  | .intro _ _ g => g

@[simp, grind =]
theorem approx_eta {α : TypeVec n} {k} (x : CofixA P α (k + 1)) :
    .intro (head' x) (content' x) (children' x) = x := by
  cases x; rfl

def truncate {α : TypeVec n} : ∀ {k}, CofixA P α (k + 1) → CofixA P α k
  | 0, _                 => .continue
  | _ + 1, .intro a f g => .intro a f (truncate ∘ g)

end Defs

/--
`Agree x y` holds when `x` and `y` share the same tag, same non-recursive content,
and each subtree of `x` agrees with the corresponding subtree of `y`.
-/
inductive Agree {α : TypeVec n} : ∀ {k}, CofixA P α k → CofixA P α (k + 1) → Prop
  | continu (x : CofixA P α 0) (y : CofixA P α 1) : Agree x y
  | intro {k} {a : P.A} {f : P.drop.B a ⟹ α}
      (g  : P.last.B a → CofixA P α k)
      (g' : P.last.B a → CofixA P α (k + 1))
      (h  : ∀ i, Agree (g i) (g' i))
      : Agree (.intro a f g) (.intro a f g')

@[simp, grind .]
theorem agree_trivial {α : TypeVec n} {x : CofixA P α 0} {y : CofixA P α 1} :
    Agree P x y := .continu x y

@[grind →]
theorem head_of_agree {α : TypeVec n} {k} {x : CofixA P α (k + 1)} {y : CofixA P α (k + 2)}
    (h : Agree P x y) : head' x = head' y := by
  cases h; rfl

@[grind →]
theorem content_of_agree {α : TypeVec n} {k} {x : CofixA P α (k + 1)} {y : CofixA P α (k + 2)}
    (h : Agree P x y) : content' x ≍ content' y := by
  cases h; rfl

@[grind .]
theorem children_of_agree {α : TypeVec n} {k} {x : CofixA P α (k + 1)} {y : CofixA P α (k + 2)}
    {i j} (h₀ : i ≍ j) (h₁ : Agree P x y) :
    Agree P (children' x i) (children' y j) := by
  obtain - | ⟨g, g', hagree⟩ := h₁; cases h₀; apply hagree

theorem truncate_eq_of_agree {α : TypeVec n} {k} (x : CofixA P α k) (y : CofixA P α (k + 1))
    (h : Agree P x y) : truncate y = x := by
  induction k with
  | zero     => cases x; cases y; rfl
  | succ k ih =>
    obtain - | ⟨g, g', hagree⟩ := h
    simp only [truncate, Function.comp_def]; congr 1; funext i; exact ih _ _ (hagree i)

def AllAgree {α : TypeVec n} (x : ∀ k, CofixA P α k) : Prop :=
  ∀ k, Agree P (x k) (x (k + 1))

def sCorec {α : TypeVec.{u} n} {β : Type u} (g : β → P (α ::: β)) :
    β → ∀ k, CofixA P α k
  | _, 0      => .continue
  | b, k + 1 => .intro (g b).fst (dropFun (g b).snd) (fun j => sCorec g (lastFun (g b).snd j) k)

theorem agree_corec {α : TypeVec.{u} n} {β : Type u} (g : β → P (α ::: β))
    (b : β) (k : Nat) : Agree P (sCorec P g b k) (sCorec P g b (k + 1)) := by
  induction k generalizing b with
  | zero      => constructor
  | succ k ih => exact .intro _ _ (fun j => ih _)

end Approx

open Approx

structure MIntl (α : TypeVec.{u} n) where
  approx     : ∀ k, CofixA P α k
  consistent : AllAgree P approx

/-- The M-type (greatest fixpoint) of `P`, parameterized by `α : TypeVec n` -/
def M (α : TypeVec.{u} n) : Type u := MIntl P α

namespace Approx

protected def sMk {α : TypeVec n} (x : P (α ::: M P α)) : ∀ k, CofixA P α k
  | 0      => .continue
  | k + 1  => .intro x.fst (dropFun x.snd) (fun j => (lastFun x.snd j).approx k)

protected theorem P_mk {α : TypeVec n} (x : P (α ::: M P α)) : AllAgree P (Approx.sMk P x) := by
  intro k
  cases k with
  | zero    => constructor
  | succ k  => exact .intro _ _ (fun j => (lastFun x.snd j).consistent k)

end Approx

namespace M
variable {P}

@[ext]
theorem ext {α : TypeVec n} {x y : M P α} (h : ∀ k, x.approx k = y.approx k) : x = y := by
  cases x; cases y; congr 1; funext k; exact h k

def head {α : TypeVec n} (x : M P α) : P.A :=
  head' (x.approx 1)

def content {α : TypeVec n} (x : M P α) : P.drop.B x.head ⟹ α :=
  content' (x.approx 1)

@[simp, grind =]
theorem head'_approx {α : TypeVec n} (x : M P α) (k : Nat) :
    head' (x.approx (k + 1)) = x.head := by
  induction k with
  | zero      => rfl
  | succ k ih => grind [x.consistent (k + 1)]

def children {α : TypeVec n} (x : M P α) (j : P.last.B (x.head)) : M P α where
  approx k     := children' (x.approx (k + 1)) (cast (by grind) j)
  consistent k := by grind [x.consistent (k + 1)]

section Lemmas

@[grind =]
theorem content'_approx {α : TypeVec n} (x : M P α) (k : Nat) :
    content' (x.approx (k + 1)) ≍ x.content := by
  induction k with
  | zero      => rfl
  | succ k ih => grind [x.consistent (k + 1)]

end Lemmas

/-! ## Constructor, Destructor and Corecursor-/

variable (P) in
/-- Constructor -/
def mk {α : TypeVec n} (x : P (α ::: M P α)) : M P α where
  approx     := Approx.sMk P x
  consistent := Approx.P_mk P x

/-- Destructor -/
def dest {α : TypeVec n} (x : M P α) : P (α ::: M P α) :=
  ⟨x.head, splitFun x.content x.children⟩

variable (P) in
/-- Corecursor -/
def corec {α : TypeVec.{u} n} {β : Type u} (g : β → P (α.append1 β)) (b : β) : M P α where
  approx     := Approx.sCorec P g b
  consistent := Approx.agree_corec P g b

/-! ### Ctor / dtor / corec Lemmas -/
section Lemmas

@[simp, grind =]
theorem dest_mk {α : TypeVec n} (x : P (α ::: M P α)) :
    dest (mk P x) = x := by
  obtain ⟨a, f⟩ := x
  simp only [dest, mk, head, content, Approx.sMk, head', content']
  congr 1
  rw [← split_dropFun_lastFun f]; congr 1

@[simp, grind =]
theorem mk_dest {α : TypeVec n} (x : M P α) : mk P (dest x) = x := by
  apply ext; intro k
  induction k with
  | zero => apply Subsingleton.elim
  | succ k _ =>
    rcases hx : x.approx (k + 1) with _ | ⟨a, f, g⟩
    obtain rfl : a = x.head := by
      have h : head' (x.approx (k + 1)) = a := by grind [head']
      grind
    obtain rfl : f = x.content := by
      have h : content' (x.approx (k + 1)) ≍ f := by grind [content']
      grind
    obtain rfl : g = fun i => (x.children i).approx k := by
      funext j
      have h : children' (x.approx (k + 1)) (cast (by grind) j) ≍ g j := by
        generalize hj : cast _ j = j'
        replace hj : j ≍ j' := by grind
        revert hj j'
        rw [hx, children']
        grind
      grind [children]
    rfl

@[simp, grind =]
theorem approx_mk {α : TypeVec n} (a : P.A) (f : P.drop.B a ⟹ α)
    (g : P.last.B a → M P α) (k : Nat) :
    (mk P ⟨a, splitFun f g⟩).approx (k + 1) = .intro a f (fun j => (g j).approx k) := by
  simp only [mk, Approx.sMk, dropFun_splitFun, lastFun_splitFun]

/-! ### Corec component lemmas -/

@[simp, grind =]
theorem head_corec {α : TypeVec.{u} n} {β : Type u} (g : β → P (α.append1 β)) (b : β) :
    (corec P g b).head = (g b).fst := rfl

@[simp, grind =]
theorem content_corec {α : TypeVec.{u} n} {β : Type u} (g : β → P (α.append1 β)) (b : β) :
    (corec P g b).content = dropFun (g b).snd := rfl

@[simp, grind =]
theorem children_corec {α : TypeVec.{u} n} {β : Type u} (g : β → P (α.append1 β)) (b : β) :
    (corec P g b).children = fun j => corec P g (lastFun (g b).snd j) := by
  rfl

@[simp, grind =]
theorem dest_corec {α : TypeVec.{u} n} {β : Type u} (g : β → P (α.append1 β)) (b : β) :
    dest (corec P g b) = (id ::: (corec P g)) <$$> (g b) := by
  simp only [dest, head_corec, content_corec, children_corec]
  congr 1
  rw [← split_dropFun_lastFun (g b).snd]
  simp only [dropFun_splitFun, TypeVec.id_comp, appendFun_comp_splitFun]
  rfl

end Lemmas

/-! ## Bisimulation -/

/--
Bisimilarity: `x` and `y` are bisimilar if they share the same head
and non-recursive content,
and each pair of corresponding children is again bisimilar.
-/
coinductive IsBisim {α : TypeVec n} : M P α → M P α → Prop where
  | step {x y : M P α} {a : P.A} {f : P.drop.B a ⟹ α} {g g' : P.last.B a → M P α} :
        dest x = ⟨a, splitFun f g⟩ → dest y = ⟨a, splitFun f g'⟩
        → (∀ i, IsBisim (g i) (g' i))
        → IsBisim x y

/-- Bisimulation principle: bisimilar M-type elements are equal. -/
theorem bisim {α : TypeVec n} {x y : M P α} (h : IsBisim x y) : x = y := by
  apply ext; intro k
  induction k generalizing x y with
  | zero => apply Subsingleton.elim
  | succ k ih =>
    cases h
    have : x = mk P x.dest := by grind
    have : y = mk P y.dest := by grind
    grind

/-! ## Advanced Corec Lemmas -/

@[simp, grind =]
theorem corec_dest (x : P.M α) : corec P dest x = x := by
  apply bisim
  apply IsBisim.coinduct (fun y x => y = corec P dest x)
  · rintro _ x rfl
    refine ⟨x.head, x.content, fun i => corec P dest (x.children i), x.children, ?_⟩
    simp [dest]
    rfl
  · grind

end M
end MvPFunctor
end QpfTypes
