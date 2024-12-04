import Mathlib.Data.QPF.Multivariate.Constructions.Comp
import Mathlib.Data.QPF.Multivariate.Constructions.Prj
import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Qpf.Macro.Comp

namespace MvQPF

/-!
  # DeepThunk

  `DeepThunk` corresponds approximately to the [trace](https://ncatlab.org/nlab/show/traced+monoidal+category) of a given polynomial functor.
  These allows the original pfunctor to inject into them allowing for the most general state of a co-recursive principle.

  ## Stronger generaliziation

  Currently a functor defined as `F := cofix f α in α` would generate the DeepThunk `DT := cofix f (β ⊕ α) in α`.
  This could be generalized to `DT := cofix f ( (β ⊕ α) × (F → F) )` which would allow for modifying the returned value of a deeper call.
  Note this is still a QPF as (F → F) is constant, also note the function could not be (F → DT) as this would be unproductive
  (think of the function that simply skips the first value then yields a recursive construct).
  This generaliziation would be useful in expression streams of for example the natural numbers as:

  codef nats : Colist ℕ := .cons 0 (nats.map Nat.succ)

  which would be productive though strange. This generalizes to nested guarded recursive structures.
  Unproductive unguarded structures are limited in the same way they currently are.

  Even more general this could take a vector of a given length of continuation and a function from a vector of that length of Fs and output a single F.
  This would allow for a lot more recursive calls to also be implemented.
-/

/--
  This is a fresh sum-type that represents the actions that can be taken within a `DeepThunk`.
  These we're previously represented as a sum type but this lead to issues when trying to detect it in a macro so we prefer a fresh type
-/
inductive DTSum (α β : Type u) : Type u
  /-- Hand responsibility back to the co-recursor -/
  | recall (v : α)
  /-- Continue constructing a DeepThunk -/
  | cont   (v : β)

namespace DTSum

def equivSum : DTSum α β ≃ α ⊕ β where
  toFun
    | .recall a => .inl a
    | .cont   a => .inr a
  invFun
    | .inl a => .recall a
    | .inr a => .cont a

  left_inv  := by rintro (_|_) <;> rfl
  right_inv := by rintro (_|_) <;> rfl

abbrev Uncurried := @TypeFun.ofCurried 2 DTSum

def equiv {Γ} : Uncurried Γ ≃ QpfSum' Γ := equivSum.trans MvQPF.Sum.equiv

end DTSum

open DTSum in
instance : MvFunctor DTSum.Uncurried where
  map f := equiv.invFun ∘ Sum.SumPFunctor.map f ∘ equiv.toFun

open DTSum in
instance : MvQPF DTSum.Uncurried :=
  .ofEquiv (fun _ => equiv)

namespace DeepThunk

/--
  This function handles the composition by replacing the first arg with the new DTSum value.
  One could see this being implemented as a Vec.append1 but this would force n > 0 which just makes expressing the rest of these values quite painful
-/
abbrev innerMapper : Vec (TypeFun (n.succ)) n
  | .fz => Comp DTSum.Uncurried !![Prj 1, Prj 0]
  | .fs n => Prj (n.add 2)

/-- If `F` is `Cofix G α`, then `hoFunctor F` is `Cofix G (DTSum β α)` -/
abbrev hoFunctor (F : TypeFun n) : TypeFun (n + 1) := Comp F innerMapper

instance : MvFunctor (!![Prj 1, @Prj (n + 2) 0] j) := by
  rcases j with _|_|_|_
  <;> simp only [Vec.append1]
  <;> infer_instance

instance : MvQPF (!![Prj 1, @Prj (n + 2) 0] j) := by
  rcases j with _|_|_|_
  <;> simp only [Vec.append1]
  <;> infer_instance

instance {i : Fin2 n} : MvFunctor (innerMapper i) := by cases i <;> infer_instance
instance {i : Fin2 n} : MvQPF (innerMapper i)     := by cases i <;> infer_instance

abbrev Uncurried (F : TypeFun n) [MvFunctor F] [MvQPF F] := Cofix (hoFunctor F)

/--
  Between the original functor and the ⊕-composed functor there is an injection,
  it occurs by taking the right step at every point co-recursively.

  The instances of the hof will have this defined as a coercion.
-/
def inject
  {F : TypeFun n.succ} {α : TypeVec n}
  [inst : MvFunctor F] [MvQPF F] : Cofix F α → DeepThunk.Uncurried F (α ::: β) :=
  MvQPF.Cofix.corec fun v => by
    let v := Cofix.dest v

    have : (hoFunctor F (α.append1 β ::: Cofix F α)) = F (α.append1 (DTSum β (Cofix F α))) := by
      simp only [hoFunctor, Comp]
      congr
      funext i
      simp only [innerMapper, TypeVec.append1]
      cases i <;> rfl
    rw [this]

    have arr : TypeVec.Arrow (α ::: Cofix F α) (α ::: (DTSum β (Cofix F α))) :=
      fun | .fz => fun a => by
              simp only [TypeVec.append1] at a
              simp only [TypeVec.append1]
              exact .cont a
          | .fs n => id

    exact inst.map arr v

/--
  `DeepThunk.corec` is a co-recursive principle allowing partially yielding results.
  It achives this by changing the recursive point to either the usual argument to the deeper call,
  or continuing the structure.
-/
def corec
    {F : TypeFun n.succ} {α : TypeVec n}
    [inst : MvFunctor F] [MvQPF F]
    (f : β → Uncurried F (α ::: β))
    : β → Cofix F α
  := (Cofix.corec fun v => by
    have v := Cofix.dest v

    have : hoFunctor F (α.append1 β ::: Cofix (hoFunctor F) (α ::: β)) = F (α ::: (DTSum β (Cofix (hoFunctor F) (α.append1 β)))) := by
      simp only [hoFunctor, Comp]
      congr
      funext i
      simp only [innerMapper, TypeVec.append1]
      cases i <;> rfl
    rw [this] at v

    have : TypeVec.Arrow (α ::: (DTSum β (Cofix (hoFunctor F) (α ::: β)))) (α ::: Cofix (hoFunctor F) (α ::: β)) := fun
      | .fz => fun | .recall x => f x | .cont x => x
      | .fs _ => id

    exact MvFunctor.map this v
  ) ∘ f

end DeepThunk
/--
  `DeepThunk` is a higher-order functor used for partially yielding results in co-recursive principles.
  It is defined by taking the cofix-point of the composition of the ⊕-functor and the `Base` functor.
  For using this in co-recursive functions see `DeepThunk.corec`
  -/
abbrev DeepThunk (F : TypeFun n) [MvFunctor F] [MvQPF F] := DeepThunk.Uncurried F |> TypeFun.curried

end MvQPF
