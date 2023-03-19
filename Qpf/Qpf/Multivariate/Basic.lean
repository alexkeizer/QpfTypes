import Mathlib.Data.QPF.Multivariate.Basic
import Qpf.Util.TypeFun

variable {n} {F : TypeFun n}

namespace MvQPF
  instance instQPF_ofCurried_curried [q : MvQPF F] : 
      MvQPF <| TypeFun.ofCurried <| F.curried := 
    by rw[TypeFun.ofCurried_curried_involution]; exact q

  instance instIsPolynomial_ofCurried_curried [p : IsPolynomial F] : 
      IsPolynomial <| TypeFun.ofCurried <| F.curried := 
    by rw[TypeFun.ofCurried_curried_involution]; exact p

end MvQPF