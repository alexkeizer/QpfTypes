import Mathlib.Data.QPF.Multivariate.Basic
import Qpf.Util.TypeFun
import Qpf.Util.VecClass


section 
  variable {m : Nat}

  class MvQPFVecClass {n : Nat} (v : Vec (TypeFun m) n) where 
    prop_func : ∀ i, MvFunctor (v i)
    prop : ∀ i, MvQPF (v i)

  namespace MvQPFVecClass
    /-- In case of an empty `Vec`, the statement is vacuous -/
    instance instNil (G : Vec (TypeFun m) 0) : MvQPFVecClass G
      := ⟨(by intro i; cases i), (by intro i; cases i)⟩

    /-- 
      The recursive step, if the head and all elements in the tail of a vector implement `Class`,
      then all elements implement `Class`. 
      Requires that `v` is reducible by type class inference.    
    -/
    instance instSucc {n : Nat} (G : Vec (TypeFun m) (.succ n)) 
                                [zero_func : MvFunctor (G .fz)]
                                [zero : MvQPF (G .fz)]
                                /-  It is important that the vector used in the recursive step remains 
                                    reducible, or the inference system will not find the appropriate 
                                    instance. That is why we spell out the composition, rather than 
                                    use the more concise `v ∘ .fs`                              
                                -/
                                [succ : MvQPFVecClass (fun i => G i.fs)] : 
                            MvQPFVecClass G := 
    ⟨(by
      intro i;
      cases i;
      exact zero_func;
      apply succ.prop_func
    ),
    (by intro i; 
        cases i; 
        exact zero;
        apply succ.prop
      )⟩


    /-- 
      Alternative recursive step. Since `Vec.append1` is not reducible, we explicitly provide an
      instance
    -/
    instance instAppend1 {n : Nat} (tl : Vec (TypeFun m) n) (hd : TypeFun m)
                                [zero_func : MvFunctor hd]
                                [zero : MvQPF hd]
                                [succ : MvQPFVecClass tl] : 
                            MvQPFVecClass (tl.append1 hd) := 
    ⟨(by 
      intro i; 
      cases i; 
      exact zero_func;
      apply succ.prop_func
    ),
    (by intro i; 
        cases i; 
        exact zero;
        apply succ.prop
      )⟩


    /-- Users need not be aware of `VecClass`, they can simply write universally quantified type class 
        constraints  -/
    instance instUnboxFunc {n : Nat} {G : Vec (TypeFun m) n} [inst : MvQPFVecClass G] : 
      ∀i, MvFunctor (G i) :=
    inst.prop_func

    instance instUnbox {n : Nat} {G : Vec (TypeFun m) n} [inst : MvQPFVecClass G] : 
      ∀i, MvQPF (G i) :=
    inst.prop

    instance instBox {n : Nat} {G : Vec (TypeFun m) n} [inst_func : ∀i, MvFunctor (G i)] [inst : ∀i, MvQPF (G i)] : 
      MvQPFVecClass G :=
    ⟨inst_func, inst⟩
  end MvQPFVecClass
end
