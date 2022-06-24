import Qpf
open MvQpf

/-!
  Let us start with a simple example of an inductive type: lists
  ```lean4
  inductive QpfList (α : Type u)
   | nil : QpfList α 
   | cons : α →  QpfList α → QpfList α
  ```

  Since each argument to each constructor is purely a variable, or purely the resulting type `QpfList α`,
  we can translate this type to a fixpoint of some polynomial functor, which we'll call `QpfList.Shape`.

  Since we'll be taking a fixpoint, `QpfList.Shape` is indeed a binary functor, where the first argument
  will be passed on as `α`, and the second argument will be representing `QpfList α`.
  We can think of it like the following (non-recursive!) inductive type
  ```lean4
  inductive QpfList.Shape' (α β : Type u)
    | nil  : Shape' α β
    | cons : α → β → Shape' α β
  ```

  Of course, we won't actually define the type as such, instead, recall that polynomial functors are
  encoded by a "head" type, which may not depend on `α`, and a "child" type, that does depend on `α`.

-/ 
namespace QpfList
  /- 
    The aforementioned "head" type is a simple enumeration of all constructors  
  -/
  inductive HeadT
    | nil
    | cons

  /- 
    The "child" type tells us for each constructor (i.e., element of `HeadT`) and each type argument,
    how many instances of that type we need, through the cardinality of `ChildT a i`.

    In this case, the `nil` constructor takes no argument, while `cons` takes one instance of both 
    arguments, hence we use the empty and unit types, respectively.
  -/
  abbrev ChildT : HeadT → TypeVec 2
    | HeadT.nil , _ => Empty
    | HeadT.cons, _ => Unit

  /- 
    We define the polynomial functor
  -/
  abbrev P := MvPFunctor.mk HeadT ChildT

  /- The `MvFunctor` instance is defined on `P` action on objects-/
  abbrev F := P.Obj

  /-
    Of course, each polynomial functor is a (multivariate) quotient of a polynomial functor, and
    this is automatically inferred
  -/
  example : MvQpf F := 
    by infer_instance


  /-
    We define `QpfList'` as the fixpoint of `P` in the last argument
  -/
  abbrev QpfList' : TypeFun 1
    := Fix QpfList.F

  /-
    And define a curried version for final use
  -/
  abbrev QpfList
    := QpfList'.curried

  
  example : MvQpf QpfList' := 
    by infer_instance


/-
  # Constructors
  We manually define the constructors in terms of `Fix.mk`
-/
  
  def nil {α : Type} : QpfList α :=
    Fix.mk ⟨HeadT.nil, fun _ emp => by contradiction⟩

  
  def cons {α} (hd : α) (tl : QpfList α) : QpfList α :=
    Fix.mk ⟨HeadT.cons, fun i _ => match i with
                          | 0 => tl
                          | 1 => hd
    ⟩


  -- The list `[1, 2, 3]`
  example : QpfList Nat :=
    cons 1 $ cons 2 $ cons 3 $ nil

  /-
    Pattern matching does not work like one would expect, but we'll ignore it for now

  def mul2 : QpfList Nat → QpfList Nat
    | nil        => nil
    | cons hd tl => cons (2*hd) (mul2 tl)
  -/


  -- def rec {α} 
  --         {motive : QpfList α → Sort _} 
  --         : (motive nil) 
  --         → ((hd : α) → (tl : QpfList α) → motive (cons hd tl))
  --         → (t : QpfList α) 
  --         → motive t := 
  -- fun base_case rec_case t => by
  --   let t' := Fix.dest t;
  --   simp [MvPFunctor.Obj] at t'
  --   rcases t' with ⟨a, f⟩
  --   cases a <;> simp [MvPFunctor.B] at f
    
    
    -- let g := fun ⟨a, f⟩ => match a with
    --   | HeadT.nil  => cast (
    --                     by  delta nil;
    --                         apply congrArg; apply congrArg;
    --                         simp [MvFunctor.map];
    --                         conv in (fun x emp => _) => {
    --                           tactic => funext x y; contradiction;
    --                         }                             
    --                   ) base_case
    --   | HeadT.cons => by simp [MvPFunctor.B, HeadT, ChildT] at f
    --                      skip
    --                      sorry
                      -- cast (
                      --   _
                      -- ) (rec_case (f (Fin2.fz) (by simp [P.B])) _)
    -- Fix.drec (β := motive) g t

  
end QpfList

export QpfList (QpfList QpfList')