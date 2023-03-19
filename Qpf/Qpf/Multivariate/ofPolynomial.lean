import Mathlib
import Qpf.Util
import Qpf.Macro.Tactic.FinDestr

/-!
  This file provides a way to show some typefunction `F` is a QPF by establishing an isomorphism 
  to some polynomial functor `P`

  This is especially useful to show functoriality of external type functions, which are not
  easily redefined in terms of `MvPFunctor`
-/

namespace MvQPF
  /-- If `F` is isomorphic to a QPF `F'`, then `F` is also a QPF -/
  def ofIsomorphism {F : TypeFun n} 
                    (F' : TypeFun n)
                    [q : MvQPF F']
                    (box    : ∀{α}, F α → F' α) 
                    (unbox  : ∀{α}, F' α → F α) 
                    (box_unbox_id : ∀{α} (x : F' α), box (unbox x) = x)
                    (unbox_box_id : ∀{α} (x : F α), unbox (box x) = x 
                                  := by intros; rfl
                                )
                  : MvQPF F
    where
      P           := q.P
      map f a     := unbox <| q.map f <| box a
      abs         := unbox ∘ q.abs
      repr        := q.repr ∘ box
      abs_repr    := by 
                      intros  
                      simp only [q.abs_repr, unbox_box_id, Function.comp]
      abs_map f x := by 
                      dsimp
                      apply congrArg
                      simp [box_unbox_id, q.abs_map]

  /-- If `F` is isomorphic to a polynomial functor `P'`, then `F` is a QPF -/
  def ofPolynomial  {F : TypeFun n} 
                    (P : MvPFunctor n)
    := @ofIsomorphism _ F P.Obj _
  

end MvQPF