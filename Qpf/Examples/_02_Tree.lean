import Qpf
import Qpf.Examples._01_List

open MvQpf

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
  inductive QpfTree.Shape (α β : Type)
  | node : α → β  → QpfTree.Shape α β γ
  ```
-/


namespace QpfTree
  namespace Shape
    /-
      Since there is only one constructor, `def HeadT := Unit` would also have sufficed
    -/
    inductive HeadT
      | node

    abbrev ChildT : HeadT → TypeVec 2
      | _, _ => Unit

    abbrev P := MvPFunctor.mk HeadT ChildT

    abbrev F := P.Obj.curried
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

  def F_manual : TypeFun 2
    := Comp Shape.P.Obj ![
        Prj 1,
        MvQpf.Comp QpfList' ![Prj 0]
    ]

  /-
    There is also a `#qpf` command, which will define the right projections and compositions for us!
  -/
  #qpf F_curried α β := Shape.F α (QpfList β)

  /-
    The command will give us a curried type function, the internal, uncurried, function can be found
    under `.typefun`
  -/
  #check (F_curried : Type _ → Type _ → Type _)

  abbrev F := F_curried.typefun

  #check (F : TypeFun 2)


  /-
    Type class inference works as expected, it can reason about the vectors of functors involved
    in compositions
  -/
  example : MvQpf F := by infer_instance

  abbrev QpfTree' := Fix F
  abbrev QpfTree  := QpfTree'.curried

  /-
  ## Constructor

  We'd like to take `QpfList (QpfTree α)` as an argument, since that is what users expect.
  However, `Fix.mk` expects something akin to `(Comp QpfList' ![Prj 0]) ![_, QpfTree' ![α]]`,
  which is not definitionally equal, so we'll have to massage the types a bit
  -/


  def node (a : α) (children : QpfList (QpfTree α)) : QpfTree α :=
    Fix.mk ⟨Shape.HeadT.node, 
            fun i _ => match i with
            | 0 => cast (by
                      unfold QpfList; unfold QpfTree
                      unfold TypeFun.curried
                      simp only [TypeFun.curriedAux, TypeFun.reverseArgs]
                      simp only [Vec.append1, Vec.reverse]
                      simp only [Prj, Comp]
                      apply congrArg

                      funext j; 
                      match j with
                      | .fs _ => contradiction
                      | .fz =>
                        simp only [Fin2.inv, Fin2.last, Vec.append1, TypeVec.append1, Vec.reverse]
                    ) children                    
            | 1 => a
    ⟩

  /-
    Even though there are some `sorry`s left in the formalization codebase, all of the machinery
    for inductive types is fully proven, and indeed, we can construct `QpfTree` without depending
    on `sorryAx`
  -/
  #print axioms node
  
end QpfTree

export QpfTree (QpfTree QpfTree')