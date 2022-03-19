
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

end Set