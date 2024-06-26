import Qpf
import Qpf.Examples._01_List

import Qpf.Util.FinCompat

open MvQPF

/-
  # Rose trees
  Now let us look at Rose Trees, that is, trees where each node has a label of type `α` and an arbitrary
  number of children.

  ```lean4
  inductive QpfTree (α : Type)
  | node : α → QpfList (QpfTree α) → QpfTree α
  ```

  First, we extract the shape functor. That is, we replace each distinct expression (which is not
  already a type variable) with a new type variable.
  In this case, that is only `QpfList (QpfTree α)`, which we represent with `β`

  ```lean4
  inductive QpfTree.Shape (α β ρ: Type)
  | node : α → β  → QpfTree.Shape α β ρ
  ```
-/

theorem falsum : False := sorry

theorem totally_legit_proof : FermatsLastTheorem = False.elim falsum

#print axioms falsum

data QpfTreeEx α 
  | node : α → QpfList (QpfTreeEx α) → QpfTreeEx α

#print QpfTreeEx.Uncurried
#print axioms QpfTreeEx
/- #print prefix QpfTreeEx -/

namespace QpfTree
  namespace Shape
    /-
      Since there is only one constructor, `def HeadT := Unit` would also have sufficed
    -/
    inductive HeadT
      | node

    abbrev ChildT : HeadT → TypeVec 3
      | .node => ![PFin2 1, PFin2 1, PFin2 0]

    abbrev P := MvPFunctor.mk HeadT ChildT

    abbrev F := P.Obj
    /- abbrev F := P.Obj -/
  end Shape

  /-
    Before we can take the fixpoint, we need to compose this shape functor with QpfList in the second
    argument. Effectively, we want to define
    ```
      F α β := Shape.F α (QpfList β)
    ```

    Note that we don't care too much about whether `F` is a polynomial functor, we just require it
    to be a QPF, so we'll invoke the composition of QPFs here.

    To do so, we have to supply two binary functors to be composed with `Shape.P.Obj`.
    The first functor is trivial, it's the projection to the second argument (we count the
    arguments right-to-left, since that is how the `Vec`s are built).
    ```
      G₁ α β := α           -- (hence, G₁ := Prj 1)
    ```
    The second functor is a bit more involved. We want to invoke `QpfList`, which expects a single
    argument, but `G₂` should be a binary functor. Additionally, the argument we want to apply
    `QpfList` to is `β`, the second argument, so we compose `QpfList` with a projection functor
    ```
      G₂ α β := QpfList β   -- (hence, G₂ := Comp QpfList' ![Prj 0])
    ```
  -/

  abbrev Base : TypeFun 2
    := Comp Shape.P.Obj (toFin2F ![
        Prj 1,
        Comp QpfList' (toFin2F ![Prj 0]),
        Prj 0
    ])
/-

  MvFunctor
    (Comp (TypeFun.ofCurried ?m.3211)
      (Vec.append1
        (Vec.append1 (Vec.append1 Vec.nil (Prj (Fin2.fs Fin2.fz)))
          (Comp (TypeFun.ofCurried QpfList) (Vec.append1 Vec.nil (Prj Fin2.fz))))
        (Prj Fin2.fz))) : Type 1
but is expected to have types
-/

  /- set_option trace.QPF true in -/
  /- /- -/
  /-   There is also a `qpf` command, which will define the right projections and compositions for us! -/
  /- -/ -/
  /- qpf F_curried α ρ := (TypeFun.curried Shape.F) α (QpfList ρ) ρ -/

#print F_curried.Uncurried
  /- abbrev F_curried := Base -/

  -- TODO: Prove that these are the same
  /- example : Base = TypeFun.ofCurried F_curried := by { sorry } -/
  /-
    The command will give us a curried type function, the internal, uncurried, function can be found
    under `.Uncurried`
  -/

  abbrev F := TypeFun.ofCurried F_curried

  /-
    Type class inference works as expected, it can reason about the vectors of functors involved
    in compositions
  -/
  /- example : MvQPF F := by infer_instance -/

  abbrev QpfTree' := Fix F
  abbrev QpfTree  := TypeFun.curried QpfTree'

  /-
  ## Constructor

  -- We'd like to take `QpfList (QpfTree α)` as an argument, since that is what users expect.
  -- However, `Fix.mk` expects something akin to `(Comp QpfList' ![Prj 0]) ![_, QpfTree' ![α]]`,
  -- which is not definitionally equal, so we'll have to massage the types a bit
  -/


  def node (a : α) (children : QpfList (QpfTree α)) : QpfTree α :=
    Fix.mk ⟨Shape.HeadT.node,
            fun i _ => match i with
            | 0 => children
                    -- by
                    -- apply cast ?_ children;
                    -- unfold QpfList;
                    -- dsimp only [TypeFun.curried, TypeFun.curriedAux, TypeFun.reverseArgs]
                    -- apply congrArg
                    -- vec_eq;
            | 1 => a
    ⟩

  /-
    Even though there are some `sorry`s left in the formalization codebase, all of the machinery
    for inductive types is fully proven, and indeed, we can construct `QpfTree` without depending
    on `sorryAx`
  -/

end QpfTree

export QpfTree (QpfTree QpfTree')
