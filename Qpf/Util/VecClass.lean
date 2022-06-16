import Qpf.Qpf.Multivariate.Basic

/-
  # Type Classes on Vecs
  Since a `Vec` contains finitely many elements, statements of the form `∀i, Class (v i)`
  can be inferred using induction on the length of `Vec`s.


  A reasonable first attempt could be as follows
  ```lean4
  instance VecClass_nil' (v : Vec α 0) : VecClass' Class v
    := by intro i; cases i

  -- We have to set this option because `Class` might not be a type class
  set_option checkBinderAnnotations false in
  instance VecClass_succ'  (v : Vec α (.succ n)) 
                              [zero : Class (v .fz)]
                              [succ : VecClass' Class (fun i => v i.fs)] : 
                          VecClass' Class v := 
  by intro i; 
      cases i; 
      exact zero;
      apply succ
  ```

  And this is accepted by lean, but fails to correctly infer for vectors with more than one element
  ```lean4

  /-- The vector `![Nat]` -/
  abbrev v₁ : Vec Type 1 := fun i => Nat

  /-- The vector `![Nat, Int]` -/
  abbrev v₂ : Vec Type 2 
    | .fz     => Nat
    | .fs .fz => Int

  /-- Works! -/
  example : ∀i, Inhabited (v₁ i) :=
    by infer_instance

  /-- Failed to syntesize instance -/
  example : ∀i, Inhabited (v₂ i) :=
    by infer_instance
  ```

  Instead, we "box" these universally quantified statements in a new type class `VecClass`
  -/
namespace Vec
    -- `Class` is intended to range over (unary) typeclasses, but there is nothing preventing
    -- users to instantiate it with non-typeclass functions
    variable {α : Type _} {n : Nat}
  
  /-- A custom type class to express that all elements of `v` implement some typeclass `Class` -/
  class VecClass (Class : α → Type _) (v : Vec α n) where
    prop : ∀ i, Class (v i)

  variable {α : Type _} {Class : α → Type} {n : Nat}


  /-- In case of an empty `Vec`, the statement is vacuous -/
  instance VecClass_nil (v : Vec α 0) : VecClass Class v
    := ⟨by intro i; cases i⟩

  -- Since `Class` might not be a typeclass, Lean will complain we're putting
  -- it in the `[...]` inference binder, the following option turns this warning off.
  -- If a user tries to instantiate this definition in the case that `Class` is *not*
  -- a typeclass, Lean will throw an `type class instance expected` error
  set_option checkBinderAnnotations false in
  /-- 
    The recursive step, if the head and all elements in the tail of a vector implement `Class`,
    then all elements implement `Class`. 
    Requires that `v` is reducible by type class inference.

    It is important that the vector used in the recursive step (`succ`) remains reducible, or the
    inference system will not find the appropriate instance. That is why we spell out the composition,
    rather than use the more concise `v ∘ .fs`
  -/
  instance VecClass_succ  (v : Vec α (.succ n)) 
                              [zero : Class (v .fz)]
                              [succ : VecClass Class (fun i => v i.fs)] : 
                          VecClass Class v := 
  ⟨by intro i; 
      cases i; 
      exact zero;
      apply succ.prop
    ⟩


  set_option checkBinderAnnotations false in
  /-- 
    Alternative recursive step. Since `Vec.append1` is not reducible, we explicitly provide an
    instance
  -/
  instance VecClass_append1 (tl : Vec α n) (hd : α)
                              [zero : Class hd]
                              [succ : VecClass Class tl] : 
                          VecClass Class (tl.append1 hd) := 
  ⟨by intro i; 
      cases i; 
      exact zero;
      apply succ.prop
    ⟩


  /-- Users need not be aware of `VecClass`, they can simply write universally quantified type class 
      constraints  -/
  instance VecClass_unbox [inst : VecClass Class v] : 
    ∀i, Class (v i) :=
  inst.prop
end Vec