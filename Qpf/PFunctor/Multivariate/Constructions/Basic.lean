import Qpf.Qpf.Multivariate.Basic


#check MvPFunctor


def MvPFunctor.mk' {n : Nat} (ctors : List (Vec Nat n)) : MvPFunctor n
  :=  let A := PFin2 ctors.length
      let B := fun a i => PFin2 (ctors.get (a.toFin) i)
      ⟨A, B⟩
    
