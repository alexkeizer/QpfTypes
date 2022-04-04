
namespace Sigma
  variable {α α₁ α₂ : Type _} {β : α → Type _} {β₁ : α₁ → Type _} {β₂ : α₂ → Type _}

  @[simp] theorem eta : ∀ x : Σ a, β a, Sigma.mk x.1 x.2 = x
  | ⟨i, x⟩ => rfl
end Sigma