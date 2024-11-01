import Lean
import Qq

import Mathlib.Data.QPF.Multivariate.Constructions.Comp
import Mathlib.Data.QPF.Multivariate.Constructions.Const
import Mathlib.Data.QPF.Multivariate.Constructions.Prj
import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Mathlib.Data.QPF.Multivariate.Constructions.Fix

import Qpf.Util.TypeFun

/-!
## QpfExpr

We build an abstraction to bundle a Lean expression of type `TypeFun n` with
the corresponding `MvQPF` instance, and define methods for the various
constructions under which QPFs are closed ((co)fixpoints, composition, etc.).
-/

open Lean Qq

/-- A Lean expression of type `TypeFun n`, with a bundled `MvQPF` instance -/
inductive QpfExpr (u : Level) (n : Nat)
  | qpf
      (F : Q(TypeFun.{u, u} $n))
      (qpf : Q(MvQPF $F) := by exact q(inferInstance))
  /- TODO: add a pfunctor special case, as follows:
  /-- In `.pfunctor P`, `P` is a Lean Expr of type `MvPFunctor n`.
  This is a specialization, which serves to preserve the fact that a QPF is
  actually polynomial -/
  | pfunctor (P : Expr)
  -/
deriving Inhabited

/-! ## Preliminaries -/
section ToExpr

def Fin2.toExpr {n : Nat} : Fin2 n → Q(Fin2 $n)
  | .fz   => q(Fin2.fz)
  | .fs i => q(Fin2.fs $(toExpr i))
instance {n : Nat} : ToExpr (Fin2 n) where
  toExpr      := Fin2.toExpr
  toTypeExpr  := q(Fin2 $n)

def Vec.toExpr {α : Q(Type u)} : {n : Nat} → Vec Q($α) n → Q(Vec $α $n)
  | 0,   _  => q(Vec.nil)
  | _+1, as =>
    let a : Q($α) := as.last
    let as := toExpr as.drop
    q(Vec.append1 $as $a)
instance {α : Q(Type u)} {n : Nat} : ToExpr (Vec Q($α) n) where
  toExpr      := Vec.toExpr
  toTypeExpr  := q(Vec $α $n)

def DVec.toExpr {n : Nat} {αs : Q(Fin2 $n → Type u)} (xs : DVec (fun (i : Fin2 n) => Q($αs $i))) :
    Q(DVec.{u} $αs) :=
  match n with
  | 0   => q(Fin2.elim0)
  | _+1 =>
    let a : Q($αs 0) := xs.last
    let as := toExpr xs.drop
    q(fun
      | .fz   => $a
      | .fs i => $as i
    )

end ToExpr

namespace QpfExpr

/-! ## Basic Definitions -/

/-- The raw type function, i.e., an expression of type `TypeFun n` -/
def typeFun {n : Nat} : QpfExpr u n → Q(TypeFun.{u, u} $n)
  | qpf F _ => F

/-- The bundled QPF instance, i.e., an expression of type `MvQPF ($typeFun)` -/
def qpfInstance {n : Nat} : (q : QpfExpr u n) → Q(MvQPF $q.typeFun)
  | qpf _ q => q


variable {m} [Monad m] [MonadLiftT MetaM m] in
/-- Construct a `QPFExpr` from an expression of type `TypeFun n`, by
synthesizing the corresponding MvQPF instance.

Throws an error if synthesis fails. -/
def ofTypeFun {n : Nat} (F : Q(TypeFun.{u, u} $n)) : m (QpfExpr u n) := do
  let qpf ← synthInstanceQ q(MvQPF $F)
  return QpfExpr.qpf F qpf

/-- cast a `QpfExpr u n` to be of arity `m`, assuming that `n` and `m` are
actually equal. Returns `none` if `n ≠ m` -/
def cast? {n m} (e : QpfExpr u n) : Option (QpfExpr u m) :=
  if h : n = m then
    some (h ▸ e)
  else
    none

/-- check that the expressions contained in an QpfExpr have the correct types -/
def check : QpfExpr u n → MetaM Unit
  | qpf F q => do
    F.check
    q.check

/-! ## Tracing-/

def toMessageData : QpfExpr u n → MessageData
  | qpf F q => m!"qpf ({F}) ({q})"
instance : ToMessageData (QpfExpr u n) := { toMessageData }

/-! ## Constructions -/

/-! ### Basic Functors (Constants and Projections) -/

/-- A constant functor, see `MvQPF.Const` -/
def const (n : Nat) (A : Q(Type u)) : QpfExpr u n :=
  qpf q(MvQPF.Const $n $A)

/-- `prj i` is a functor that projects to the i-th argument, see `MvQPF.Prj` -/
def prj {u : Level} {n : Nat} (i : Fin2 n) : QpfExpr u n :=
  qpf q(MvQPF.Prj $i)

/-! ### (Co)Fixpoint -/

/-- The (inductive) fixpoint of a QPF, see `MvQPF.Fix` -/
def fix : QpfExpr u (n+1) → QpfExpr u n
  | qpf F _q => qpf q(MvQPF.Fix $F)

/-- The (coinductive) cofixpoint of a QPF, see `MvQPF.Cofix` -/
def cofix : QpfExpr u (n+1) → QpfExpr u n
  | qpf F _q => qpf q(MvQPF.Cofix $F)

/-! ### Composition -/

/--
Our automation needs to refer to this instance by name.
Since the name of this instances might change, we define our own aliasses.
-/
private def instMvQPFComp (F : TypeFun n) (Gs : Fin2 n → TypeFun m)
    [q : MvQPF F] [qG : ∀ i, MvQPF (Gs i)] :
    MvQPF (MvQPF.Comp F Gs) := by
  infer_instance

/-- Compositions of QPFs, see `MvQPF.comp` -/
def comp (F : QpfExpr u n) (Gs : Vec (QpfExpr u m) n) : QpfExpr u m :=
  let GExpr : Q(Vec (TypeFun.{u,u} $m) $n) :=
    Vec.toExpr (fun i => (Gs i).typeFun)
  let GQpf : Q(∀ i, MvQPF.{u,u} ($GExpr i)) :=
    let αs := q(fun i => MvQPF.{u,u} ($GExpr i))
    @DVec.toExpr _ _ αs (fun i => (Gs i).qpfInstance)

  let comp := q(@MvQPF.Comp $n _ $F.typeFun $GExpr)
  let qpfInstance := q(
    @instMvQPFComp (q := $F.qpfInstance) (qG := $GQpf)
  )
  qpf comp qpfInstance
