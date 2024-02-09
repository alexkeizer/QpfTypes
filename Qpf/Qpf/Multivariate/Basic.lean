import Mathlib.Data.QPF.Multivariate.Basic
import Qpf.Util.TypeFun

namespace MvQPF
  /--
    A QPF is polynomial, if it is equivalent to the underlying `MvPFunctor`.
    `repr_abs` is the last property needed to show that `abs` is an isomorphism, with `repr`
    its inverse
  -/
  class IsPolynomial {n} (F : TypeVec n → Type _) [MvFunctor F] extends MvQPF F where
    repr_abs : ∀ {α} (x : P.Obj α), repr (abs x) = x
  #align mvqpf.is_polynomial MvQPF.IsPolynomial


  namespace IsPolynomial
    variable {n : ℕ} {F : TypeVec n → Type _}

    /--
      Show that the desired equivalence follows from `IsPolynomial`
    -/
    def equiv [MvFunctor F] [p : IsPolynomial F] :
      ∀ α, F α ≃ p.P.Obj α
    := fun _ => {
      toFun := p.repr,
      invFun := p.abs,
      left_inv := p.abs_repr,
      right_inv := p.repr_abs,
    }
    #align mvqpf.is_polynomial.equiv MvQPF.IsPolynomial.equiv

    def ofEquiv (P : MvPFunctor n) (eqv : ∀ {α}, F α ≃ P.Obj α) [functor : MvFunctor F] (map_eq : ∀ (α β : TypeVec n) (f : TypeVec.Arrow α β) (x : F α), functor.map f x = (eqv.invFun <| P.map f <| eqv.toFun <| x) := by intros; rfl) : IsPolynomial F where
      P         := P
      abs       := eqv.invFun
      repr      := eqv.toFun
      abs_repr  := eqv.left_inv
      abs_map   := by intros;
                      simp only [Equiv.invFun_as_coe, map_eq, Equiv.toFun_as_coe,
                                 Equiv.apply_symm_apply, Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq];
                      rfl
      repr_abs  := eqv.right_inv

  end IsPolynomial

end MvQPF

namespace MvPFunctor
  variable {n : Nat} (P : MvPFunctor n)

  /--
    Every polynomial functor is trivially a QPF
  -/
  instance : MvQPF P.Obj :=
  {
    P         := P,
    abs       := id,
    repr      := id,
    abs_repr  := by intros; rfl,
    abs_map   := by intros; rfl,
  }

  /--
    Every polynomial functor is a polynomial QPF
  -/
  instance : MvQPF.IsPolynomial P.Obj :=
  {
    repr_abs := by intros; rfl
  }

end MvPFunctor


variable {n} {F : TypeFun n}

namespace MvQPF
  instance instMvFunctor_ofCurried_curried [f : MvFunctor F] :
      MvFunctor <| TypeFun.ofCurried <| F.curried := 
    by rw[TypeFun.ofCurried_curried_involution]; exact f

  instance instQPF_ofCurried_curried [functor : MvFunctor F] [q : MvQPF F] : 
      MvQPF <| TypeFun.ofCurried <| F.curried :=
    by 
      apply cast ?_ q
      congr
      . rw[TypeFun.ofCurried_curried_involution]
      . exact (cast_heq _ _).symm

  instance instIsPolynomial_ofCurried_curried [functor : MvFunctor F] [p : IsPolynomial F] : 
      IsPolynomial <| TypeFun.ofCurried <| F.curried := 
    by 
      apply cast ?_ p
      congr
      . rw[TypeFun.ofCurried_curried_involution]
      . exact (cast_heq _ _).symm

end MvQPF

