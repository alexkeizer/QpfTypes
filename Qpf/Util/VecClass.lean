import Lean
import Qpf.Util.Vec

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

-- `Class` is intended to range over (unary) typeclasses, but there is nothing preventing
    -- users to instantiate it with non-typeclass functions
    variable {α : Type _} {n : Nat}

namespace Vec

open Lean Meta in
/-- Derive a quantified version of the provided typeclass, so that statements of the form 
    `∀i, Class (v i)` can be synthesized
 -/
macro "derive_vec_class" Class:ident type:term : command => 
  let VecClass := mkIdent <| Class.getId ++ "VecClass"
  `(
    class $VecClass {n : Nat} (v : Vec $type n) where
      prop : ∀ i, $Class (v i)

    namespace $VecClass
      /-- In case of an empty `Vec`, the statement is vacuous -/
      instance instNil (G : Vec $type 0) : $VecClass G
        := ⟨by intro i; cases i⟩


      /-- 
        The recursive step, if the head and all elements in the tail of a vector implement `Class`,
        then all elements implement `Class`. 
        Requires that `v` is reducible by type class inference.    
      -/
      instance instSucc {n : Nat} (G : Vec $type (.succ n)) 
                                  [zero : $Class (G .fz)]
                                  /-  It is important that the vector used in the recursive step remains 
                                      reducible, or the inference system will not find the appropriate 
                                      instance. That is why we spell out the composition, rather than 
                                      use the more concise `v ∘ .fs`                              
                                  -/
                                  [succ : $VecClass (fun i => G i.fs)] : 
                              $VecClass G := 
      ⟨by intro i; 
          cases i; 
          exact zero;
          apply succ.prop
        ⟩


      /-- 
        Alternative recursive step. Since `Vec.append1` is not reducible, we explicitly provide an
        instance
      -/
      instance instAppend1 {n : Nat} (tl : Vec $type n) (hd : $type)
                                  [zero : $Class hd]
                                  [succ : $VecClass tl] : 
                              $VecClass (tl.append1 hd) := 
      ⟨by intro i; 
          cases i; 
          exact zero;
          apply succ.prop
        ⟩


      /-- Users need not be aware of `VecClass`, they can simply write universally quantified type class 
          constraints  -/
      instance instUnbox {n : Nat} {G : Vec $type n} [inst : $VecClass G] : 
        ∀i, $Class (G i) :=
      inst.prop

      instance instBox {n : Nat} {G : Vec $type n} [inst : ∀i, $Class (G i)] : 
        $VecClass G :=
      ⟨inst⟩
    end $VecClass
  )
end Vec

