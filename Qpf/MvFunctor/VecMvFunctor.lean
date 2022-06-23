import Qpf.MvFunctor

/-!
  The following is mostly a specialization of `VecClass`, since `MvFunctor` does not fit in the
  `Class : α → Type` signature (it takes an implicit argument). 
-/

/-- A "boxed" type class to express that all elements of `G` implement `MvFunctor` -/
class VecMvFunctor (G : Vec (TypeFun m) n) where
  prop : ∀ i, MvFunctor (G i)

namespace VecMvFunctor


  /-- In case of an empty `Vec`, the statement is vacuous -/
  instance instNil (G : Vec (TypeFun m) 0) : VecMvFunctor G
    := ⟨by intro i; cases i⟩

  /-- 
    The recursive step, if the head and all elements in the tail of a vector implement `Class`,
    then all elements implement `Class`. 
    Requires that `v` is reducible by type class inference.    
  -/
  instance instSucc  (G : Vec (TypeFun m) (.succ n)) 
                              [zero : MvFunctor (G .fz)]
                              /-  It is important that the vector used in the recursive step remains 
                                  reducible, or the inference system will not find the appropriate 
                                  instance. That is why we spell out the composition, rather than 
                                  use the more concise `v ∘ .fs`                              
                              -/
                              [succ : VecMvFunctor (fun i => G i.fs)] : 
                          VecMvFunctor G := 
  ⟨by intro i; 
      cases i; 
      exact zero;
      apply succ.prop
    ⟩


  /-- 
    Alternative recursive step. Since `Vec.append1` is not reducible, we explicitly provide an
    instance
  -/
  instance instAppend1 (tl : Vec (TypeFun m) n) (hd : TypeFun m)
                              [zero : MvFunctor hd]
                              [succ : VecMvFunctor tl] : 
                          VecMvFunctor (tl.append1 hd) := 
  ⟨by intro i; 
      cases i; 
      exact zero;
      apply succ.prop
    ⟩


  -- /-- Users need not be aware of `VecMvFunctor`, they can simply write universally quantified type class 
  --     constraints  -/
  instance instUnbox [inst : VecMvFunctor G] : 
    ∀i, MvFunctor (G i) :=
  inst.prop

  instance instBox [inst : ∀i, MvFunctor (G i)] :
    VecMvFunctor G := ⟨inst⟩

end VecMvFunctor

