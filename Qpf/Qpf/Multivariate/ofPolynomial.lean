import Mathlib.Data.QPF.Multivariate.Basic
import Qpf.Util
import Qpf.Macro.Tactic.FinDestr

/-!
  This file provides a way to show some typefunction `F` is a QPF by establishing an isomorphism 
  to some polynomial functor `P`

  This is especially useful to show functoriality of external type functions, which are not
  easily redefined in terms of `MvPFunctor`
-/

namespace MvFunctor 
  /-- If `F` is isomorphic to a MvFunctor `F'`, then `F` is also a MvFunctor -/
  def ofIsomorphism {F : TypeFun n}
                    (F' : TypeFun n)
                    [q : MvFunctor F']
                    (box    : ∀{α}, F α → F' α) 
                    (unbox  : ∀{α}, F' α → F α) 
                  : MvFunctor F
    where
      map f a     := unbox <| q.map f <| box a
end MvFunctor

namespace MvQPF
  /-- If `F` is isomorphic to a QPF `F'`, then `F` is also a QPF -/
  def ofIsomorphism {F : TypeFun n} 
                    (F' : TypeFun n)
                    [functor' : MvFunctor F']
                    [functor : MvFunctor F]
                    [q : MvQPF F']
                    (box    : ∀{α}, F α → F' α) 
                    (unbox  : ∀{α}, F' α → F α) 
                    (box_unbox_id : ∀{α} (x : F' α), box (unbox x) = x)
                    (unbox_box_id : ∀{α} (x : F α), unbox (box x) = x 
                                  := by intros; rfl
                                )
                    (map_eq : ∀ (α β : TypeVec n) (f : TypeVec.Arrow α β) (a : F α), functor.map f a = (unbox <| functor'.map f <| box a) := by intros; rfl)
                  : MvQPF F
    where
      P           := q.P
      abs         := unbox ∘ q.abs
      repr        := q.repr ∘ box
      abs_repr    := by 
                      intros  
                      simp only [q.abs_repr, unbox_box_id, Function.comp]
      abs_map f x := by 
                      dsimp
                      rw [map_eq]
                      apply congrArg
                      simp [box_unbox_id, q.abs_map]

  /-- If `F` is isomorphic to a polynomial functor `P'`, then `F` is a QPF -/
  def ofPolynomial  {F : TypeFun n} 
                    (P : MvPFunctor n)
    := @ofIsomorphism _ F P.Obj 
  

end MvQPF
