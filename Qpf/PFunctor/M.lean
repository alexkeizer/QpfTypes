
import Qpf.PFunctor.Basic

namespace PFunctor
open Nat

-- def M (P : pfunctor.{u}) : Type u

-- def M_dest : M P → P.obj (M P)

-- def M_corec : (α → P.obj α) → (α → M P)
-- theorem M_dest_corec (g : α → P.obj α) (x : α) :
-- M_dest (M_corec g x) = M_corec g <$> g x
-- theorem M_bisim (r : M P → M P → Prop)
-- (h : ∀ x y, r x y →
-- ∃ a f g, M_dest x = ha, fi ∧ M_dest y = ha, gi ∧ ∀ i, r (f i) (g i)) :
-- ∀ x y, r x y → x = y

variable (P: PFunctor.{u})

inductive M_approx : Nat → Type u
  | continu   : M_approx 0
  | intro {n} : ∀ a, (P.B a → M_approx n) → M_approx (n + 1)

inductive agree : ∀ {n : Nat}, M_approx P n → M_approx P (n+1) → Prop
  | continu (x : M_approx P 0) (y : M_approx P 1)  : agree x y
  | intro {n} {a} (x : P.B a → M_approx P n) (y : P.B a → M_approx P (n+1)) :
    (∀ i, agree (x i) (y i)) → agree (M_approx.intro a x) (M_approx.intro a y)



structure M := 
  (approx : ∀ n, M_approx P n) 
  (agrees : ∀ n, agree P (approx n) (approx (n+1)))

end PFunctor