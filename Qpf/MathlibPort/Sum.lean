
namespace Sum
  def bind {e α β : Type u} : e ⊕ α → (α → e ⊕ β) → e ⊕ β
  := fun s f => match s with
      | inl x => inl x
      | inr a => f a

  /-- Define a function on `α ⊕ β` by giving separate definitions on `α` and `β`. -/
  protected def elim {α β γ : Sort _} (f : α → γ) (g : β → γ) 
    : α ⊕ β → γ
  | inl x => f x
  | inr x => g x

end Sum

instance {α} : Bind (Sum α) 
  := ⟨@Sum.bind α⟩