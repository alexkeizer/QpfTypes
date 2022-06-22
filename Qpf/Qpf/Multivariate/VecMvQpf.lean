import Qpf.Qpf.Multivariate.Basic

/-!
  The following is mostly a specialization of `VecClass`, since `MvQpf` does not fit in the
  `Class : α → Type` signature (it takes an implicit argument). 
-/

/-- A "boxed" type class to express that all elements of `G` implement `MvQpf` -/
class VecMvQpf (G : Vec (TypeFun m) n) [∀i, MvFunctor (G i)] where
  prop : ∀ i, MvQpf (G i)

namespace VecMvQpf


  /-- In case of an empty `Vec`, the statement is vacuous -/
  instance instNil (G : Vec (TypeFun m) 0) [∀i, MvFunctor (G i)] : VecMvQpf G
    := ⟨by intro i; cases i⟩

  /-- 
    The recursive step, if the head and all elements in the tail of a vector implement `Class`,
    then all elements implement `Class`. 
    Requires that `v` is reducible by type class inference.    
  -/
  instance instSucc  (G : Vec (TypeFun m) (.succ n)) 
                              [∀i, MvFunctor (G i)]
                              [zero : MvQpf (G .fz)]
                              /-  It is important that the vector used in the recursive step remains 
                                  reducible, or the inference system will not find the appropriate 
                                  instance. That is why we spell out the composition, rather than 
                                  use the more concise `v ∘ .fs`                              
                              -/
                              [succ : VecMvQpf (fun i => G i.fs)] : 
                          VecMvQpf G := 
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
                              [zeroF : MvFunctor hd]
                              [succF : ∀i, MvFunctor (tl i)]
                              [zero : MvQpf hd]
                              [succ : VecMvQpf tl] : 
                          VecMvQpf (tl.append1 hd) := 
  ⟨by intro i; 
      cases i; 
      exact zero;
      apply succ.prop
    ⟩


  /-- Users need not be aware of `VecMvQpf`, they can simply write universally quantified type class 
      constraints  -/
  instance instUnbox [∀i, MvFunctor (G i)] [inst : VecMvQpf G] : 
    ∀i, MvQpf (G i) :=
  inst.prop

  instance instBox [∀i, MvFunctor (G i)] [inst : ∀i, MvQpf (G i)] : 
    VecMvQpf G :=
  ⟨inst⟩
end VecMvQpf