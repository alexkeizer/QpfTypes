import Qpf.PFunctor.Basic

namespace PFunctor
open PFunctor

variable {P : PFunctor}

inductive W (P : PFunctor)
  | mk (a : P.A) (f : P.B a → W P) : W P


/- inhabitants of W types is awkward to encode as an instance
assumption because there needs to be a value `a : P.A`
such that `P.B a` is empty to yield a finite tree -/
-- attribute [nolint has_Inhabited_instance] W


/-- root element  of a W tree -/
def W.head : W P → P.A
| ⟨a, f⟩ => a

/-- children of the root of a W tree -/
def W.children : ∀ x : W P, P.B (W.head x) → W P
| ⟨a, f⟩ => f

/-- destructor for W-types -/
def W.dest : W P → obj P (W P)
| ⟨a, f⟩ => ⟨a, f⟩

@[simp] theorem W.dest_mk (p : obj P (W P)) : W.dest (W.mk p.fst p.snd) = p :=
by cases p; rfl

@[simp] theorem W.mk_dest (p : W P) : W.mk (W.dest p).fst (W.dest p).snd = p :=
by cases p; rfl

end PFunctor