
import Qpf.Mathlib
import Mathlib.Init.Set

namespace Set

@[simp] theorem mem_univ (x : α) : x ∈ @univ α := trivial

section Range

variable {f : ι → α}

open Function

/-- Range of a function.

This function is more flexible than `f '' univ`, as the image requires that the domain is in Type
and not an arbitrary Sort. -/
def range (f : ι → α) : Set α :=
  { x | ∃ y, f y = x }

@[simp] theorem mem_range {x : α} : x ∈ range f ↔ ∃ y, f y = x := Iff.rfl

end Range


@[simp]
theorem image_univ {f : α → β} : image f univ = range f := 
by
  ext x
  simp [image, range]

@[simp]
theorem mem_set_of_eq {a : α} {p : α → Prop} : (a ∈ { a | p a }) = p a :=
  rfl

@[ext]
theorem ext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
by funext x
   simp [h]
   apply h

theorem SubSet.antisymm {a b : Set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
Set.ext $ λ x => ⟨@h₁ _, @h₂ _⟩



end Set