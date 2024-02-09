import Mathlib.Control.Functor.Multivariate
import Qpf.Util.TypeFun
import Qpf.Util.VecClass


section 
  variable {m : Nat}

  derive_vec_class MvFunctor (TypeFun m)
end
