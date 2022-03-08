
inductive fin' : Nat → Type
| raise {n : Nat} : fin' n → fin' n.succ
| last {n : Nat} : fin' n.succ

namespace fin'

def elim0 {α} : fin' 0 → α 
  := λ emp => by cases emp

/-- There is only one function with empty domain `fin' 0` -/
def eq_fn0 {α} (f g : fin' 0 → α) : f = g := 
by funext i; cases i

/-- There is only one function with empty domain `fin' 0`
    We take `fin'.elim0` to be the "normalized" such function
 -/ 
@[simp] def eq_fn0_elim0 {α} (f g : fin' 0 → α) : f = fin'.elim0
  := by apply eq_fn0

/- FIXME
def succ_cases {n : Nat} (i : Fin (n + 1)) : PSum {j : Fin n // i = j.cast_succ} (i = Fin.last n) :=
by
  cases i
  -- cases i with i h
  -- by_cases h' : i < n
  -- { left, refine ⟨⟨i, h'⟩, _⟩, apply eq_of_veq, reflexivity }
  -- right, apply eq_of_veq,
  -- show i = n, from 
  -- le_antisymm (nat.le_of_lt_succ h) (le_of_not_lt h')
-/

end fin'