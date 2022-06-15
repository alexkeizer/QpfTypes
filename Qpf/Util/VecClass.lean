import Qpf.Qpf.Multivariate.Basic

section
    -- `Class` is intended to range over (unary) typeclasses, but there is nothing preventing
    -- users to instantiate it with non-typeclass functions
    variable {α : Type _}

    /-- `VecClassAux k Class v` means that all but the last `k` 
        elements of `v` implement `Class` -/
    class VecClassAux (k : Nat) (Class : α → Type) {n : Nat} (v : Vec α (n+k)) where
      inst : ∀i : Fin2 n, Class (v <| i.add k)

    /-- `VecClass Class v` means that all element of `v` implement `Class` -/
    abbrev VecClass (Class : α → Type) {n : Nat} (v : Vec α n)
      := @VecClassAux α 0 Class n v

    variable {Class : α → Type _}


    /-- Base case, all element of a en empty vec vacuosly implement every typeclass -/
    -- Does not work
    -- instance instVecNil {v : Fin2 k → α}  : 
    --   ∀ i : Fin2 0, Class (v <| i.add' k) := 
    -- by intro i; contradiction

    instance instVecNil₂ {v : Fin2 0 → α}  : 
      ∀ i : Fin2 0, Class (v i) := 
    by intro i; contradiction;

    -- instance instVecNil' {v : Fin2 k → α}  : 
    --   VecClass Class v := 
    -- by constructor; intro i; contradiction

    example (fF' : Vec (TypeFun 2) 0) : 
      ∀i, MvFunctor (fF' i) := 
    by 
      infer_instance

    -- Since `Class` might not be a typeclass, Lean will complain we're putting
    -- it in the `[...]` inference binder, the following option turns this warning off.
    -- If a user tries to instantiate this definition in the case that `Class` is *not*
    -- a typeclass, Lean will throw an `type class instance expected` error
    set_option checkBinderAnnotations false

    -- open Lean Lean.Meta Lean.Tactic
    -- elab "infer_vec_zero" : tactic => do
    --   evalTactic

    #check Lean.Parser.Tactic.simp

    -- #check Lean.Elab.Tactic.

    open Lean Lean.Parser.Tactic Lean.Elab.Tactic Lean.Meta in
    elab "whnf_infer_instance" : tactic => do 
        match <- getMainTarget with
          | Expr.app tc arg@(Expr.app v i ..) .. => do
              let target := mkApp tc (<-whnf arg);
              liftMetaTactic fun mvarId => do
                let target_mvar ← mkFreshExprMVar (some target)
                assignExprMVar mvarId target_mvar
                pure [target_mvar.mvarId!]
              evalTactic <|<- `(tactic| infer_instance)
          | _ => do
            evalTactic <|<- `(tactic| infer_instance)
            <|> throwError "Goal is not in the expected format:\n Class (v i) "
   
    -- instance instVecAppend1 
    --           {n : Nat} 
    --           {v : Fin2 n.succ → α} 
    --           [succ: ∀ i : Fin2 n, Class (v ∘ Fin2.fs <| i)] 
    --           (zero: Class (v Fin2.fz) := by zero_infer) : 
    --   ∀ i, Class (v i)
    -- | Fin2.fz   => zero
    -- | Fin2.fs i => succ i

    instance instVecAppend1MvFunctor  
        {n : Nat} 
        {v : Fin2 n.succ → (TypeFun m)}
        [succ: ∀ i : Fin2 n, MvFunctor (v ∘ Fin2.fs <| i)] 
        -- (zero: MvFunctor (v Fin2.fz) := by zero_infer) : 
        (zero: MvFunctor (v Fin2.fz) := by zero_infer) : 
      ∀i, MvFunctor (v i)
    | Fin2.fz   => zero
    | Fin2.fs i => succ i


    set_option pp.rawOnError true

    example (F : TypeFun m) [MvFunctor F] :
      let v := Vec.append1 Vec.nil F;
      ∀i : Fin2 1, MvFunctor <| v i :=
    by
      -- infer_instance
      exact instVecAppend1MvFunctor;

    example (F₁ F₂ : TypeFun m) [MvFunctor F₁] [MvFunctor F₁] :
      let v := ((Vec.append1 Vec.nil F₂).append1 F₁);
      ∀i : Fin2 2, MvFunctor <| v i :=
    by
      exact instVecAppend1MvFunctor;
      infer_instance


    -- instance instVecAppend1 {n : Nat} (k : Nat := 0)
    --           {v : Fin2 (n + 1 + k) → α} 
    --           [succ: ∀ i : Fin2 n, Class (v <| (i.fs).add k)] 
    --           [zero: Class (v <| (@Fin2.fz n).add k)] : 
    --   ∀ i : Fin2 (n + 1) , Class (v <| i.add k)
    -- | Fin2.fz   => zero
    -- | Fin2.fs i => succ i
  end