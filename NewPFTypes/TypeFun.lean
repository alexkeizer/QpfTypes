import NewPFTypes.TypeVec

/-!
# TypeFun Typeclass

`TypeFun n α` is implemented whenever the type `α` can be coerced to an `n`-ary
type function. The coercion is `TypeFun.uncurry`.
-/
namespace QpfTypes
universe u v w

/--
An instance of `TypeFun n α` shows that `α` is equivalent to an `n`-ary
type function.
-/
class TypeFun (n : outParam Nat) (α : Type w) where
  uncurry : α → TypeVec.{u} n → Type v
  curry : (TypeVec.{u} n → Type v) → α
  curry_uncurry : ∀ F, curry (uncurry F) = F := by grind
  uncurry_curry : ∀ F, uncurry (curry F) = F := by grind
open TypeFun (curry uncurry)

/-!
## Instances
-/
attribute [grind =] TypeFun.curry_uncurry TypeFun.uncurry_curry

instance : TypeFun.{u} 0 (Type v) where
  uncurry α _ := α
  curry F := F .nil
  uncurry_curry := by intro F; ext βs; simp [TypeVec.nil_eq]

instance [TypeFun.{u, v} n α] : TypeFun (n+1) (Type u → α) where
  uncurry F βs := TypeFun.uncurry (F βs.head) βs.tail
  curry F β := TypeFun.curry (fun βs => F (β <: βs))
  curry_uncurry := by intro F; ext β; simp; grind
  uncurry_curry := by intro F; ext βs; grind

instance : TypeFun n (TypeVec.{u} n → Type v) where
  uncurry F := F
  curry F := F

/-!
## Examples
-/

example (α β : Type) :
    (uncurry Sum) ((nil ::: α) ::: β) = Sum α β := by
  rfl

example (α : Type) :
    (uncurry (Sum · Unit)) (nil ::: α) = Sum α Unit := by
  rfl

/-!
## Simproc
-/
section Meta

/-
TODO: implement a (d)simproc which will:
  * match for expressions of the form `(uncurry F) (nil ::: α ::: ...)`, then
  * assert that the instance is one of the above, and if so
  * rewrite this into the more idiomatic `F α ...`
-/

end Meta
