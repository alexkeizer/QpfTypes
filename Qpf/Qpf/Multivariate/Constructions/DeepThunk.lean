import Mathlib.Data.QPF.Multivariate.Constructions.Comp
import Mathlib.Data.QPF.Multivariate.Constructions.Prj
import Mathlib.Data.QPF.Multivariate.Constructions.Cofix
import Qpf.Macro.Comp

namespace MvQPF

/-!
  # DeepThunk

  `DeepThunk` corresponds to the (co-)trace of a given polynomial functor.
  These allows the original pfunctor to inject into them allowing for the most general state of a co-recursive principle.

  ## Stronger generaliziation

  Currently the functors are mapped as follows `F := cofix f α in α` to `DT := cofix f (β ⊕ α) in α`.
  This could be generalized to `DT := cofix f ( (β ⊕ α) × (F → F) )` which would allow for modifying the returned value of a deeper call.
  Note this is still a QPF as (F → F) is constant, also note the function could not be (F → DT) as this would be unproductive
  (think of the function that simply skips the first value then yields a recursive construct).
  This generaliziation would be useful in expression streams of for example the natural numbers as:

  codef nats : Colist ℕ := .cons 0 (nats.map Nat.succ)

  which would be productive though strange. This generalizes to nested guarded recursive structures.
  Unproductive unguarded structures are limited in the same way they currently are.
-/

/--
  This is a fresh sum-type that represents the actions that can be taken within a `DeepThunk`.
  These are that a user can either

  1. recall - hand responsibility back to the co-recursor
  2. cont   - continue constructing a DeepThunk

  These we're previously represented as a sum type but  
-/
inductive DTSum (α β : Type u) : Type u
  | recall (v : α)
  | cont   (v : β)

namespace DTSum
abbrev F := @TypeFun.ofCurried 2 DTSum

def box {Γ : TypeVec 2} : F Γ → QpfSum' Γ
  | recall a => MvQPF.Sum.inl a
  | cont   b => MvQPF.Sum.inr b

def unbox {Γ : TypeVec 2} : QpfSum' Γ → F Γ
  | ⟨i, f⟩ => match i with
    | .fz   => recall (f 1 .fz)
    | .fs 0 => cont   (f 0 .fz)

def equiv {Γ} : F Γ ≃ QpfSum' Γ :=
{
  toFun   := box
  invFun  := unbox
  left_inv  := by intro x; cases x <;> rfl
  right_inv := by
    intro x
    rcases x with ⟨(i : PFin2 _), f⟩
    dsimp only [box, unbox, Sum.inl, Sum.inr]
    fin_cases i <;> {
      simp only [Function.Embedding.coeFn_mk, PFin2.ofFin2_fs, PFin2.ofFin2_fz,
        Fin2.instOfNatFin2HAddNatInstHAddInstAddNatOfNat, Nat.rec_zero]
      apply congrArg
      funext i; fin_cases i <;> (funext (j : PFin2 _); fin_cases j)
      rfl
    }
}


end DTSum

open DTSum in
instance : MvFunctor DTSum.F where
  map f x   := equiv.invFun <| Sum.SumPFunctor.map f <| equiv.toFun <| x

open DTSum in
instance : MvQPF.IsPolynomial F :=
  .ofEquiv _ equiv

namespace DeepThunk
abbrev innerMapper : Vec (TypeFun (n.succ)) n := (fun
  | .fz => Comp DTSum.F !![Prj 1, Prj 0]
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
