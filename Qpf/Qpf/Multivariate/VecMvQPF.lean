import Mathlib.Data.QPF.Multivariate.Basic
import Qpf.Util.TypeFun
import Qpf.Util.VecClass


section 
  variable {m : Nat}

  derive_vec_class MvQPF (TypeFun m)
end
