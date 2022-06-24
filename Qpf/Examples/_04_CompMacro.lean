import Qpf
import Qpf.Examples._01_List
import Qpf.Examples._02_Tree
      
/-
## Projections
-/ 

-- every qpf whose target is just a variable, gets compiled to a projection
qpf F₁ α β γ := γ

-- The supplied name is bound to the curried function
#print F₁
-- while the internal, uncurried, function is exposed as `.typefun`
#print F₁.typefun

-- We can confirm the expected results with reduce
#reduce F₁.typefun ![Nat, Int, (List Nat)]
#reduce F₁ Nat Int (List Nat)


-- Note that we can use `_` holes for unused variables
qpf F₂ α _ _ := α

#print F₂.typefun

#reduce F₂ Nat Int (List Nat)


/-
## Constants
-/
qpf F_int α β := Int

#print F_int
#print F_int.typefun

#reduce F_int Nat Nat

qpf F_list α β := QpfList Nat

#print F_list
#print F_list.typefun

#reduce F_list Nat Nat


/-
## Composition
-/ 
example : MvQpf F₁.typefun := inferInstance
example : MvQpf (TypeFun.ofCurried F₁) := inferInstance 

qpf F₃ α β := F₁ α β α

#print F₃.typefun
#reduce F₃ Nat Int




/-
  ## Dead variables

  So-called "dead" variables are non-functorial arguments.
  That is, if `F` takes three arguments, say `F α β γ`, of which one, `α`, is dead, then
  `F α` is a binary qpf, for all `α`, but `F` by itself is *not* a ternary qpf.

  A variable can be marked dead by using a bracketed binder, and all dead variables must come before
  live variables. 
-/

qpf F_dead (α : Nat) β γ := β
qpf F_dead' (α m : Nat) {a : Type} β γ := β

/-
  The following will cause a parse error, either mark `α` dead as well, or re-order the variables
  ```
  qpf F_dead' α (γ : Nat) β := β
  ```
-/


example : MvQpf (TypeFun.ofCurried $ F_dead a) := inferInstance

/-
  The following does not even typecheck. Since `α` may live in a different universe than the live
  arguments, we cannot uncurry `F_dead`
```lean4
example : MvQpf (TypeFun.ofCurried F_dead) 
  := by sorry
```
-/

/-
  A very common example of a type constructor with dead variables is that of (non-dependent)
  arrows `α → β`. It is functorial in `β`, but not in `α`
-/

-- qpf arrow {α : Type _} (a : α) β := Prod.curried a β

-- #check (Nat → Int)
-- #reduce arrow Nat Int

example (F : TypeFun 2) [q : MvQpf F] : true := by constructor

/-
  We can define functor combinators with the macro. For example, the following will flip the arguments
  to any binary qpf.
  `ToMvQpf F` is just a shorthand to say that the uncurried version of `F` implements `MvQpf`

-/
qpf flipF (F : CurriedTypeFun 2) [q : ToMvQpf F] α β := F β α