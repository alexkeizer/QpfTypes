/-
Copyright (c) 2022 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/

/-
  Some helpful lemmas about heterogenous equalities
-/

/-- Consecutive casts can be reduced to a single cast, by transitivity  -/
@[deprecated cast_cast]
theorem cast_trans {α β : Sort _} (a : α) {h₁ : α = β} {h₂ : β = γ} :
    (cast h₂ $ cast h₁ a) = cast (Eq.trans h₁ h₂) a := by
  exact cast_cast h₁ h₂ a

theorem heq_cast_left {α α' β : Sort _} (a : α) (b : β) (h : α = α') :
    HEq (cast h a) b = HEq a b := by
  subst h; simp

theorem heq_cast_right {α β β' : Sort _} (a : α) (b : β) {h : β = β'} :
    HEq a (cast h b) = HEq a b := by
  subst h; simp

theorem heq_fun_congr {α α' γ} (a : γ → α) (h : α = α') :
    HEq (fun x => (cast h $ a x)) a := by
  subst h; simp

theorem heq_cast_left_fun {α α' β γ : Type _} (a : γ → α) (b : β) (h : α = α') :
    HEq (fun x => (cast h $ a x)) b = HEq a b := by
  subst h; simp

theorem heq_cast_right_fun {α α' β γ : Type _} (a : γ → α) (b : β) (h : α = α') :
    HEq b (fun x => (cast h $ a x)) = HEq b a := by
  subst h; simp


/-
# Congruence
-/
theorem hcongr_fun {α : Sort _} {P P' : α → Sort _}
                    {f : (a : α) → P a}
                    {f' : (a : α) → P' a}
                    (a : α)
                    (H₁ : HEq f f')
                    (H₂ : P = P') :
    HEq (f a) (f' a) := by
  cases H₂; cases H₁; apply HEq.rfl;

theorem hcongr {α α' : Sort _} {P : α → Sort _} {P' : α' → Sort _}
                {f : (a : α) → P a}
                {f' : (a' : α') → P' a'}
                (a : α) (a' : α')
                (H₁ : HEq f f')
                (H₂ : HEq a a')
                (H₃ : α = α')
                (H₄ : ∀ a, P a = P' (cast H₃ a)) :
      HEq (f a) (f' a') := by
    subst H₃ H₂
    apply hcongr_fun _ H₁
    funext a
    apply H₄

/-
# Cast-related equalities
-/
theorem heq_of_eq' {α β} {a : α} {b : β} (h : β = α)  :
    a = cast h b → HEq a b := by
  intro eq;
  cases eq;
  apply cast_heq;

theorem heq_of_eq_left' {α β} {a : α} {b : β} (h : α = β)  :
    cast h a = b → HEq a b := by
  intro eq;
  apply HEq.symm;
  apply heq_of_eq' h eq.symm

theorem cast_arg  {α α' : Sort u₁}
                  {β : α → Sort u₂}
                  {β' : α' → Sort u₂}
                  {f : (a : α) → β a}
                  (a' : α')
                  (h₁ : α' = α)
                  (h₂ : ((a : α) → β a) = ((a' : α') → β' a'))
                  (h₃ : ∀ a', β (cast h₁ a') = β' a') :
    (cast (β:=(a' : α') → β' a') h₂ f) a'
    = cast (h₃ _) (f $ cast h₁ a') := by
  apply eq_of_heq;
  rw [heq_cast_right];
  apply hcongr
  . apply cast_heq
  . apply HEq.symm; apply cast_heq
  . intro a'; apply Eq.symm; apply h₃

theorem cast_arg' {α : Sort u₁} {β β' : α → Sort u₂}
                  {f : (a : α) → β a}
                  (a : α)
                  (h₁ : ((a : α) → β a) = ((a : α) → β' a))
                  (h₂ : ∀ a, β a = β' a) :
    (cast (β:=(a : α) → β' a ) h₁ f) a
    = cast (h₂ _) (f a) := by
  apply cast_arg;
  rfl


theorem cast_fun_arg {h : α = β} {f : β → γ} :
  HEq (fun (a : α) => f <| cast h a ) f :=
by
  cases h
  simp only [cast_eq, heq_eq_eq]

/-
# Function Extensionality
-/

theorem HEq.funext {α : Sort u} {β₁ β₂ : α → Sort _}
                    {f₁ : (x : α) → β₁ x}
                    {f₂ : (x : α) → β₂ x}
                    (type_eq : β₁ = β₂ )
                    :
  (∀ (x : α), HEq (f₁ x) (f₂ x)) → HEq f₁ f₂ :=
by
  cases type_eq
  intro h;
  apply heq_of_eq
  funext a
  apply eq_of_heq <| h a

theorem HEq.funext' {α₁ α₂ : Sort u} {β₁ : α₁ → Sort _} {β₂ : α₂ → Sort _}
                    {f₁ : (x : α₁) → β₁ x}
                    {f₂ : (x : α₂) → β₂ x}
                    (type_eq_α : α₁ = α₂ )
                    (type_eq_β : ∀ a, (β₁ a) = (β₂ <| cast type_eq_α a) )
                    :
  (∀ (x : α₁), HEq (f₁ x) (f₂ <| cast type_eq_α x)) → HEq f₁ f₂ :=
by
  cases type_eq_α
  apply HEq.funext
  funext x
  apply type_eq_β



section Tactic
open Lean.Parser.Tactic

/-- Calls `simp` with a bunch of theorems that are useful for simplifying heterogeneous
    equalities and casts
  -/
syntax "simp_heq" optConfig (discharger)? ("only ")? ("[" simpLemma,* "]")? (location)? : tactic
macro_rules
| `(tactic| simp_heq $cfg:optConfig $[$dis:discharger]? $[$loc:location]? )
    => `(tactic| simp $cfg $[$dis]?
                      only [cast_cast, heq_cast_left, heq_cast_right, cast_eq, cast_heq,
                        heq_cast_left_fun, heq_cast_right_fun, cast_arg', HEq.refl]
                      $[$loc]?
        )

end Tactic
