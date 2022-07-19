import Mathlib.Init.Logic
import Mathlib.Init.Function
import Mathlib.Tactic.Basic
import Mathlib.Util.LibraryNote


/-- Ex falso, the nondependent eliminator for the `PEmpty` type. -/
def PEmpty.elim {C : Sort _} : PEmpty → C 
  := fun e => by contradiction


lemma rec_heq_of_heq {α} {a b : α} {β} {C : (a' : α) → (a = a') → Sort _} {x : C a rfl} {y : β} (eq : a = b) (h : HEq x y) :
  HEq (@Eq.rec α a C x b eq) y :=
by subst eq; exact h