
def Set (α : Type u) := α → Prop
def Set.in (s : Set α) (a : α) := s a

notation:50 "{" a ":" s "|" p "}" => λ (a : s) => p

notation:50 a " ∈ " s:50           => Set.in s a
notation:40 "∀" a " ∈ " s "," p  => ∀ a, a ∈ s → p