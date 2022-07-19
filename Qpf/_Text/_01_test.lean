import Qpf
import Qpf.Macro

/-!
  The ```inductive``` keyword encompasses three concepts: sums, products, and recursion.
  Let's forget about the latter for a second, and look at a non-recursive type
-/
inductive Foo (α β γ : Type)
| bar : α → β → Foo α β γ
| qux : γ → Foo α β γ

-- data Foo' (α β γ : Type)
-- | bar : α → β → Foo' α β γ
-- | qux : γ → Foo' α β γ

/-!
  We can replace the two arguments of the ``bar`` constructor by their product.
-/

inductive Foo₂ (α β γ : Type)
| bar : (α × β) → Foo₂ α β γ
| qux : γ → Foo₂ α β γ

/-!
  Having two constructor with a single argument just means taking their sum.
-/

def Foo₃ (α β γ : Type) :=
  (α × β) ⊕ γ 

/-!
  We can make ``Foo₃`` a bit more ergonomic by defining constructor functions
-/
def Foo₃.bar {α β γ : Type} : 
  α → β → Foo₃ α β γ :=
fun a b =>
  Sum.inl (a, b)

def Foo₃.qux {α β γ : Type} :
  γ → Foo₃ α β γ :=
fun c =>
  Sum.inr c

/-!
  This is what the datatype package for Isabelle/HOL does, reducing a specification to compositions of
  just sums and products. 
  We'll use a slightly different approach, taking polynomial functors as our basic building blocks.
-/