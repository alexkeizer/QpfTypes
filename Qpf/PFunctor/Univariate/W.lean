import Qpf.PFunctor.Univariate.Basic

namespace PFunctor
open PFunctor

inductive W (P : PFunctor)
  | mk (a : P.A) (f : P.B a → W P) : W P


/- inhabitants of W types is awkward to encode as an instance
assumption because there needs to be a value `a : P.A`
such that `P.B a` is empty to yield a finite tree -/
-- attribute [nolint has_inhabited_instance] W

namespace W
variable {P : PFunctor}

/-- root element  of a W tree -/
def head : W P → P.A
| ⟨a, f⟩ => a

/-- children of the root of a W tree -/
def children : ∀ x : W P, P.B (W.head x) → W P
| ⟨a, f⟩ => f

/-- destructor for W-types -/
def dest : W P → P.Obj (W P)
| ⟨a, f⟩ => ⟨a, f⟩

@[simp] theorem dest_mk (p : P.Obj (W P)) : W.dest (W.mk p.fst p.snd) = p :=
by cases p; rfl

@[simp] theorem mk_dest (p : W P) : W.mk (W.dest p).fst (W.dest p).snd = p :=
by cases p; rfl

end W
end PFunctor