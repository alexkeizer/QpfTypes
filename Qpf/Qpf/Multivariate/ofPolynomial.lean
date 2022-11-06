import Qpf.Qpf.Multivariate.Basic
import Qpf.Macro.Tactic.FinDestr

/-!
  This file provides a way to show some typefunction `F` is a QPF by establishing an isomorphism 
  to some polynomial functor `P`

  This is especially useful to show functoriality of external type functions, which are not
  easily redefined in terms of `MvPFunctor`
-/

namespace MvQpf

  def ofPolynomial {F : TypeFun n} 
                    (P : MvPFunctor n) 
                    (box    : ∀{α}, F α → P.Obj α) 
                    (unbox  : ∀{α}, P.Obj α → F α) 
                    (box_unbox_id : ∀{α} (x : P.Obj α), box (unbox x) = x)
                    -- Technically, `unbox_box_id` is not needed for the construction
                    -- We still require it so that `ofPolynomial` can only be used when `F` is
                    -- indeed isomorphic to `P`
                    (unbox_box_id : ∀{α} (x : F α), unbox (box x) = x 
                                  := by intros; rfl
                                )
                  : MvQpf F
    where
      P           := P
      map f a     := unbox <| P.map f <| box a
      abs         := @unbox
      repr        := @box
      abs_repr    := unbox_box_id
      abs_map f x := by
                      apply congrArg
                      simp [box_unbox_id]
                      rfl

end MvQpf