/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Mario Carneiro

The M construction as a multivariate polynomial functor.
-/
import Qpf.PFunctor.Multivariate.Basic 
import Qpf.PFunctor

universe u

namespace MvPFunctor
open TypeVec

variable {n : Nat} (P : MvPFunctor.{u} (n+1))

inductive M_path : P.last.M → fin' n → Type u
| root (x : P.last.M) (a : P.A) (f : P.last.B a → P.last.M) (h : PFunctor.M_dest x = ⟨a, f⟩)
       (i : fin' n) (c : P.drop.B a i) :
    M_path x i
| child (x : P.last.M) (a : P.A) (f : P.last.B a → P.last.M) (h : PFunctor.M_dest x = ⟨a, f⟩)
      (j : P.last.B a) (i : fin' n) (c : M_path (f j) i) :
    M_path x i

def Mp : MvPFunctor n :=
{ A := P.last.M, B := P.M_path }

def M (α : TypeVec n) : Type* := P.Mp.apply α

instance mvfunctor_M : mvfunctor P.M := by delta M; apply_instance

def M_corec_shape {β : Type u}
    (g₀ : β → P.A)
    (g₂ : Π b : β, P.last.B (g₀ b) → β) :
  β → P.last.M :=
PFunctor.M_corec (λ b, ⟨g₀ b, g₂ b⟩)

def cast_dropB {a a' : P.A} (h : a = a') : P.drop.B a ⟹ P.drop.B a' :=
λ i b, eq.rec_on h b

def cast_lastB {a a' : P.A} (h : a = a') : P.last.B a → P.last.B a' :=
λ b, eq.rec_on h b

def M_corec_contents {α : TypeVec.{u} n} {β : Type u}
    (g₀ : β → P.A)
    (g₁ : Π b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : Π b : β, P.last.B (g₀ b) → β) :
  Π x b, x = P.M_corec_shape g₀ g₂ b → P.M_path x ⟹ α
| ._ b h ._ (M_path.root x a f h' i c)    :=
  have a = g₀ b,
    by { rw [h, M_corec_shape, PFunctor.M_dest_corec] at h', cases h', refl },
  g₁ b i (P.cast_dropB this i c)
| ._ b h ._ (M_path.child x a f h' j i c) :=
  have h₀ : a = g₀ b,
    by { rw [h, M_corec_shape, PFunctor.M_dest_corec] at h', cases h', refl },
  have h₁ : f j = M_corec_shape P g₀ g₂ (g₂ b (cast_lastB P h₀ j)),
    by { rw [h, M_corec_shape, PFunctor.M_dest_corec] at h', cases h', refl },
  M_corec_contents (f j) (g₂ b (P.cast_lastB h₀ j)) h₁ i c

def M_corec' {α : TypeVec n} {β : Type u}
    (g₀ : β → P.A)
    (g₁ : Π b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : Π b : β, P.last.B (g₀ b) → β) :
  β → P.M α :=
λ b, ⟨M_corec_shape P g₀ g₂ b, M_corec_contents P g₀ g₁ g₂ _ _ rfl⟩

def M_corec {α : TypeVec n} {β : Type u} (g : β → P.apply (α.append1 β)) :
  β → P.M α :=
M_corec' P
  (λ b, (g b).fst)
  (λ b, drop_fun (g b).snd)
  (λ b, last_fun (g b).snd)

def M_path_dest_left {α : TypeVec n} {x : P.last.M}
    {a : P.A} {f : P.last.B a → P.last.M} (h : PFunctor.M_dest x = ⟨a, f⟩)
    (f' : P.M_path x ⟹ α) :
  P.drop.B a ⟹ α :=
λ i c, f' i (M_path.root x a f h i c)

def M_path_dest_right {α : TypeVec n} {x : P.last.M}
    {a : P.A} {f : P.last.B a → P.last.M} (h : PFunctor.M_dest x = ⟨a, f⟩)
    (f' : P.M_path x ⟹ α) :
  Π j : P.last.B a, P.M_path (f j) ⟹ α :=
λ j i c, f' i (M_path.child x a f h j i c)

def M_dest' {α : TypeVec n} {x : P.last.M}
    {a : P.A} {f : P.last.B a → P.last.M} (h : PFunctor.M_dest x = ⟨a, f⟩)
    (f' : P.M_path x ⟹ α) :
  P.apply (α.append1 (P.M α)) :=
⟨a, split_fun (P.M_path_dest_left h f') (λ x, ⟨f x, P.M_path_dest_right h f' x⟩)⟩

def M_dest {α : TypeVec n} (x : P.M α) : P.apply (α.append1 (P.M α)) :=
P.M_dest' (sigma.eta $ PFunctor.M_dest x.fst).symm x.snd

def M_mk  {α : TypeVec n} : P.apply (α.append1 (P.M α)) → P.M α :=
M_corec _ (λ i, append_fun id (M_dest P) <$$> i)

theorem M_dest'_eq_dest' {α : TypeVec n} {x : P.last.M}
    {a₁ : P.A} {f₁ : P.last.B a₁ → P.last.M} (h₁ : PFunctor.M_dest x = ⟨a₁, f₁⟩)
    {a₂ : P.A} {f₂ : P.last.B a₂ → P.last.M} (h₂ : PFunctor.M_dest x = ⟨a₂, f₂⟩)
    (f' : P.M_path x ⟹ α) : M_dest' P h₁ f' = M_dest' P h₂ f' :=
by cases h₁.symm.trans h₂; refl

theorem M_dest_eq_dest' {α : TypeVec n} {x : P.last.M}
    {a : P.A} {f : P.last.B a → P.last.M} (h : PFunctor.M_dest x = ⟨a, f⟩)
    (f' : P.M_path x ⟹ α) : M_dest P ⟨x, f'⟩ = M_dest' P h f' :=
M_dest'_eq_dest' _ _ _ _

theorem M_dest_corec' {α : TypeVec.{u} n} {β : Type u}
    (g₀ : β → P.A)
    (g₁ : Π b : β, P.drop.B (g₀ b) ⟹ α)
    (g₂ : Π b : β, P.last.B (g₀ b) → β)
    (x : β) :
  P.M_dest (P.M_corec' g₀ g₁ g₂ x) =
    ⟨g₀ x, split_fun (g₁ x) (P.M_corec' g₀ g₁ g₂ ∘ (g₂ x))⟩ :=
rfl

theorem M_dest_corec {α : TypeVec n} {β : Type u} (g : β → P.apply (α.append1 β)) (x : β) :
  P.M_dest (P.M_corec g x) = append_fun id (P.M_corec g) <$$> g x :=
begin
  transitivity, apply M_dest_corec',
  cases g x with a f, dsimp,
  rw MvPFunctor.map_eq, congr,
  conv { to_rhs, rw [←split_drop_fun_last_fun f, append_fun_comp_split_fun] },
  refl
end

lemma M_bisim_lemma {α : TypeVec n}
  {a₁ : (Mp P).A} {f₁ : (Mp P).B a₁ ⟹ α}
  {a' : P.A} {f' : (P.B a').drop ⟹ α} {f₁' : (P.B a').last → M P α}
  (e₁ : M_dest P ⟨a₁, f₁⟩ = ⟨a', split_fun f' f₁'⟩) :
  ∃ g₁' (e₁' : PFunctor.M_dest a₁ = ⟨a', g₁'⟩),
    f' = M_path_dest_left P e₁' f₁ ∧
    f₁' = λ (x : (last P).B a'),
      ⟨g₁' x, M_path_dest_right P e₁' f₁ x⟩ :=
begin
  generalize_hyp ef : @split_fun n _ (append1 α (M P α)) f' f₁' = ff at e₁,
  cases e₁' : PFunctor.M_dest a₁ with a₁' g₁',
  rw M_dest_eq_dest' _ e₁' at e₁,
  cases e₁, exact ⟨_, e₁', split_fun_inj ef⟩,
end

theorem M_bisim {α : TypeVec n} (R : P.M α → P.M α → Prop)
  (h : ∀ x y, R x y → ∃ a f f₁ f₂,
    P.M_dest x = ⟨a, split_fun f f₁⟩ ∧
    P.M_dest y = ⟨a, split_fun f f₂⟩ ∧
    ∀ i, R (f₁ i) (f₂ i))
  (x y) (r : R x y) : x = y :=
begin
  cases x with a₁ f₁,
  cases y with a₂ f₂,
  dsimp [Mp] at *,
  have : a₁ = a₂, {
    refine PFunctor.M_bisim
      (λ a₁ a₂, ∃ x y, R x y ∧ x.1 = a₁ ∧ y.1 = a₂) _ _ _
      ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩,
    rintro _ _ ⟨⟨a₁, f₁⟩, ⟨a₂, f₂⟩, r, rfl, rfl⟩,
    rcases h _ _ r with ⟨a', f', f₁', f₂', e₁, e₂, h'⟩,
    rcases M_bisim_lemma P e₁ with ⟨g₁', e₁', rfl, rfl⟩,
    rcases M_bisim_lemma P e₂ with ⟨g₂', e₂', _, rfl⟩,
    rw [e₁', e₂'],
    exact ⟨_, _, _, rfl, rfl, λ b, ⟨_, _, h' b, rfl, rfl⟩⟩ },
  subst this, congr, ext i p,
  induction p with x a f h' i c x a f h' i c p IH generalizing f₁ f₂;
  try {
    rcases h _ _ r with ⟨a', f', f₁', f₂', e₁, e₂, h''⟩,
    rcases M_bisim_lemma P e₁ with ⟨g₁', e₁', rfl, rfl⟩,
    rcases M_bisim_lemma P e₂ with ⟨g₂', e₂', e₃, rfl⟩,
    cases h'.symm.trans e₁',
    cases h'.symm.trans e₂' },
  { exact (congr_fun (congr_fun e₃ i) c : _) },
  { exact IH _ _ (h'' _) }
end

theorem M_dest_map {α β : TypeVec n} (g : α ⟹ β) (x : P.M α) :
  P.M_dest (g <$$> x) = append_fun g (λ x, g <$$> x) <$$> P.M_dest x :=
begin
  cases x with a f,
  rw map_eq,
  conv { to_rhs, rw [M_dest, M_dest', map_eq, append_fun_comp_split_fun] },
  reflexivity
end

end MvPFunctor
