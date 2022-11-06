import Qpf.Qpf.Multivariate.Basic


def MvPFunctor.mk' {n : Nat} (ctors : List (Vec Nat n)) : MvPFunctor.{u} n
  :=  let A := PFin2.{u} ctors.length
      let B := fun a i => PFin2.{u} (ctors.get (a.toFin) i)
      ⟨A, B⟩
    
