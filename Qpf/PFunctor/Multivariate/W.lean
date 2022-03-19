/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The W construction as a multivariate polynomial functor.
-/
import Qpf.PFunctor.Multivariate.Basic
import Qpf.PFunctor

universe u v

namespace MvPFunctor
open TypeVec

variable {n : Nat} (P : MvPFunctor.{u} (n+1))

/- defines a TypeVec of labels to assign to each node of P.last.W -/
inductive W_path : P.last.W → fin' n → Type u
| root (a : P.A) (f : P.last.B a → P.last.W) (i : fin' n) (c : P.drop.B a i) :
    W_path ⟨a, f⟩ i
| child (a : P.A) (f : P.last.B a → P.last.W) (i : fin' n) (j : P.last.B a) (c : W_path (f j) i) :
    W_path ⟨a, f⟩ i

def W_path_cases_on {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W}
    (g' : P.drop.B a ⟹ α) (g : ∀ j : P.last.B a, P.W_path (f j) ⟹ α) :
  P.W_path ⟨a, f⟩ ⟹ α :=
by
  intro i
  intro
  | W_path.root _ _ _ c => exact g' i c
  | W_path.child _ _ _ j c => exact g j i c

def W_path_dest_left {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W}
    (h : P.W_path ⟨a, f⟩ ⟹ α) :
  P.drop.B a ⟹ α :=
λ i c => h i (W_path.root a f i c)

def W_path_dest_right {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W}
    (h : P.W_path ⟨a, f⟩ ⟹ α) :
  ∀ j : P.last.B a, P.W_path (f j) ⟹ α :=
λ j i c => h i (W_path.child a f i j c)

theorem W_path_dest_left_W_path_cases_on
    {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W}
    (g' : P.drop.B a ⟹ α) (g : ∀ j : P.last.B a, P.W_path (f j) ⟹ α) :
  P.W_path_dest_left (P.W_path_cases_on g' g) = g' := rfl

theorem W_path_dest_right_W_path_cases_on
    {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W}
    (g' : P.drop.B a ⟹ α) (g : ∀ j : P.last.B a, P.W_path (f j) ⟹ α) :
  P.W_path_dest_right (P.W_path_cases_on g' g) = g := rfl

theorem W_path_cases_on_eta {α : TypeVec n} {a : P.A} {f : P.last.B a → P.last.W}
    (h : P.W_path ⟨a, f⟩ ⟹ α) :
  P.W_path_cases_on (P.W_path_dest_left h) (P.W_path_dest_right h) = h :=
by funext i x; cases x; repeat rfl

theorem comp_W_path_cases_on {α β : TypeVec n} (h : α ⟹ β) {a : P.A} {f : P.last.B a → P.last.W}
    (g' : P.drop.B a ⟹ α) (g : ∀ j : P.last.B a, P.W_path (f j) ⟹ α) :
  h ⊚ P.W_path_cases_on g' g = P.W_path_cases_on (h ⊚ g') (λ i => h ⊚ g i) :=
by funext i x; cases x; repeat rfl

def Wp : MvPFunctor n :=
{ A := P.last.W, B := P.W_path }

def W (α : TypeVec n) : Type _ := P.Wp.Obj α

/- FIXME: -/
instance MvFunctor_W : MvFunctor P.W := by delta W; apply inferInstance


/-
First, describe operations on `W` as a polynomial functor.
-/

def Wp_mk {α : TypeVec n} (a : P.A) (f : P.last.B a → P.last.W) (f' : P.W_path ⟨a, f⟩ ⟹ α) :
  P.W α :=
⟨⟨a, f⟩, f'⟩

def Wp_rec {α : TypeVec n} {C : Type _}
  (g : ∀ (a : P.A) (f : P.last.B a → P.last.W),
    (P.W_path ⟨a, f⟩ ⟹ α) → (P.last.B a → C) → C) :
  ∀ (x : P.last.W) (f' : P.W_path x ⟹ α), C
| ⟨a, f⟩ => λ f' => g a f f' (λ i => Wp_rec g (f i) (P.W_path_dest_right f' i))

theorem Wp_rec_eq {α : TypeVec n} {C : Type _}
    (g : ∀ (a : P.A) (f : P.last.B a → P.last.W),
      (P.W_path ⟨a, f⟩ ⟹ α) → (P.last.B a → C) → C)
    (a : P.A) (f : P.last.B a → P.last.W) (f' : P.W_path ⟨a, f⟩ ⟹ α) :
  P.Wp_rec g ⟨a, f⟩ f' = g a f f' (λ i => P.Wp_rec g (f i) (P.W_path_dest_right f' i)) :=
rfl

-- Note: we could replace Prop by Type _ and obtain a dependent recursor

theorem Wp_ind {α : TypeVec n} {C : ∀ x : P.last.W, P.W_path x ⟹ α → Prop}
  (ih : ∀ (a : P.A) (f : P.last.B a → P.last.W)
    (f' : P.W_path ⟨a, f⟩ ⟹ α),
      (∀ i : P.last.B a, C (f i) (P.W_path_dest_right f' i)) → C ⟨a, f⟩ f') :
  ∀ (x : P.last.W) (f' : P.W_path x ⟹ α), C x f'
| ⟨a, f⟩ => λ f' => ih a f f' (λ i => Wp_ind ih _ _)

/-
Now think of W as defined inductively by the data ⟨a, f', f⟩ where
- `a  : P.A` is the shape of the top node
- `f' : P.drop.B a ⟹ α` is the contents of the top node
- `f  : P.last.B a → P.last.W` are the subtrees
 -/

def W_mk {α : TypeVec n} (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
  P.W α :=
let g  : P.last.B a → P.last.W  := λ i => (f i).fst
let g' : P.W_path ⟨a, g⟩ ⟹ α := P.W_path_cases_on f' (λ i => (f i).snd)
⟨⟨a, g⟩, g'⟩

def W_rec {α : TypeVec n} {C : Type _}
    (g : ∀ a : P.A, ((P.drop).B a ⟹ α) → ((P.last).B a → P.W α) → ((P.last).B a → C) → C) :
  P.W α → C
| ⟨a, f'⟩ =>
  let g' (a : P.A) (f : P.last.B a → P.last.W) (h : P.W_path ⟨a, f⟩ ⟹ α)
        (h' : P.last.B a → C) : C :=
      g a (P.W_path_dest_left h) (λ i => ⟨f i, P.W_path_dest_right h i⟩) h'
  P.Wp_rec g' a f'

theorem W_rec_eq {α : TypeVec n} {C : Type _}
    (g : ∀ a : P.A, ((P.drop).B a ⟹ α) → ((P.last).B a → P.W α) → ((P.last).B a → C) → C)
    (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
  P.W_rec g (P.W_mk a f' f) = g a f' f (λ i => P.W_rec g (f i)) :=
by
  unfold W_mk;
  unfold W_rec;
  simp;
  rw [Wp_rec_eq];
  simp only [W_path_dest_left_W_path_cases_on, W_path_dest_right_W_path_cases_on];
  apply congrArg;
  funext i; 
  cases (f i);
  rfl

theorem W_ind {α : TypeVec n} {C : P.W α → Prop}
    (ih : ∀ (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α),
      (∀ i, C (f i)) → C (P.W_mk a f' f)) :
  ∀ x, C x :=
by
  intro ⟨a, f⟩;
  apply @Wp_ind n P α (λ a f => C ⟨a, f⟩); simp;
  intros a f f' ih';
  simp [W_mk] at ih;
  let ih'' := ih a (P.W_path_dest_left f') (λ i => ⟨f i, P.W_path_dest_right f' i⟩);
  simp at ih''; rw [W_path_cases_on_eta] at ih'';
  apply ih'';
  apply ih'

theorem W_cases {α : TypeVec n} {C : P.W α → Prop}
    (ih : ∀ (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α), C (P.W_mk a f' f)) :
  ∀ x, C x :=
P.W_ind (λ a f' f ih' => ih a f' f)

def W_map {α β : TypeVec n} (g : α ⟹ β) : P.W α → P.W β :=
λ x => g <$$> x

theorem W_mk_eq {α : TypeVec n} (a : P.A) (f : P.last.B a → P.last.W)
    (g' : P.drop.B a ⟹ α) (g : ∀ j : P.last.B a, P.W_path (f j) ⟹ α) :
  P.W_mk a g' (λ i => ⟨f i, g i⟩) =
    ⟨⟨a, f⟩, P.W_path_cases_on g' g⟩ := rfl

theorem W_map_W_mk {α β : TypeVec n} (g : α ⟹ β)
    (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
  g <$$> P.W_mk a f' f = P.W_mk a (g ⊚ f') (λ i => g <$$> f i) :=
by
  show _ = P.W_mk a (g ⊚ f') (MvFunctor.map g ∘ f)
  have : MvFunctor.map g ∘ f = λ i => ⟨(f i).fst, g ⊚ ((f i).snd)⟩ :=
    by funext i; simp; cases (f i); rfl
  rw [this]
  have : f = λ i => ⟨(f i).fst, (f i).snd⟩ :=
    by funext x; cases (f x); rfl
  have h := MvPFunctor.map_eq P.Wp g
  rw [this, W_mk_eq, W_mk_eq, h, comp_W_path_cases_on]


-- TODO: this technical theorem is used in one place in constructing the initial algebra.
-- Can it be avoided?

@[reducible] def obj_append1 {α : TypeVec n} {β : Type _}
    (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → β) :
  P.Obj (append1 α β) :=
⟨a, split_fun f' f⟩

/- FIXME
theorem map_obj_append1 {α γ : TypeVec n} (g : α ⟹ γ)
  (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
append_fun g (P.W_map g) <$$> P.obj_append1 a f' f =
  P.obj_append1 a (g ⊚ f') (λ x => P.W_map g (f x)) :=
by
  unfold obj_append1;
  rw [map_eq];
  simp [*];
  show (g ::: W_map P g) ⊚ split_fun f' f = split_fun (g ⊚ f') fun x => W_map P g (f x);
-- by rw [apply_append1, apply_append1, map_eq, append_fun, ← split_fun_comp]; refl
-/

/-
Yet another view of the W type: as a fixed point for a multivariate polynomial functor.
These are needed to use the W-construction to construct a fixed point of a qpf, since
the qpf axioms are expressed in terms of `map` on `P`.
-/

def W_mk' {α : TypeVec n} : P.Obj (α.append1 (P.W α)) → P.W α
| ⟨a, f⟩ => P.W_mk a (drop_fun f) (last_fun f)

def W_dest' {α : TypeVec.{u} n} : P.W α → P.Obj (α.append1 (P.W α)) :=
P.W_rec (λ a f' f _ => ⟨a, split_fun f' f⟩)

theorem W_dest'_W_mk {α : TypeVec n}
    (a : P.A) (f' : P.drop.B a ⟹ α) (f : P.last.B a → P.W α) :
  P.W_dest' (P.W_mk a f' f) = ⟨a, split_fun f' f⟩ :=
by unfold W_dest'; rw [W_rec_eq]

theorem W_dest'_W_mk' {α : TypeVec n} (x : P.Obj (α.append1 (P.W α))) :
  P.W_dest' (P.W_mk' x) = x :=
by cases x; 
   unfold W_mk';
   rw [W_dest'_W_mk, split_drop_fun_last_fun]

end MvPFunctor
