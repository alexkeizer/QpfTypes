
namespace Sum
  def bind {e α β : Type u} : e ⊕ α → (α → e ⊕ β) → e ⊕ β
  := fun s f => match s with
      | inl x => inl x
      | inr a => f a
end Sum

instance {α} : Bind (Sum α) 
  := ⟨@Sum.bind α⟩