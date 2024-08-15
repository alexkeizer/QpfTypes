import Mathlib.Data.QPF.Multivariate.Constructions.Comp
import Mathlib.Data.QPF.Multivariate.Constructions.Prj
import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Qpf.Macro.Comp

namespace MvQPF

namespace DeepThunk
abbrev innerMapper : Vec (TypeFun (n.succ)) n := (fun
  | .fz => Comp Sum.Sum' !![Prj 1, Prj 0]
  | .fs n => Prj (n.add 2))

/-- The actual higher order functor taking `cofix f α in α` to `cofix f (β ⊕ α) in α` -/
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
instance {i : Fin2 n} : MvQPF (innerMapper i) := by cases i <;> infer_instance

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

    have : (hoFunctor F (α.append1 β ::: Cofix F α)) = F (α.append1 (β ⊕ Cofix F α)) := by
      simp only [hoFunctor, Comp]
      congr
      funext i
      simp only [innerMapper, TypeVec.append1]
      cases i <;> rfl
    rw [this]

    have arr : TypeVec.Arrow (α ::: Cofix F α) (α ::: (β ⊕ Cofix F α)) :=
      fun | .fz => fun a => by
              simp only [TypeVec.append1] at a
              simp only [TypeVec.append1]
              exact .inr a
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

    have : hoFunctor F (α.append1 β ::: Cofix (hoFunctor F) (α ::: β)) = F (α ::: (β ⊕ (Cofix (hoFunctor F) (α.append1 β)))) := by
      simp only [hoFunctor, Comp]
      congr
      funext i
      simp only [innerMapper, TypeVec.append1]
      cases i <;> rfl
    rw [this] at v

    have : TypeVec.Arrow (α ::: (β ⊕ (Cofix (hoFunctor F) (α ::: β)))) (α ::: Cofix (hoFunctor F) (α ::: β)) := fun
      | .fz => fun | .inl x => f x | .inr x => x
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
