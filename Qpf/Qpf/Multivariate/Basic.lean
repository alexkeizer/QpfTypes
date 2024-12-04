import Mathlib.Data.QPF.Multivariate.Basic
import Qpf.Util.TypeFun

namespace MvQPF
variable {n} {F : TypeFun n}

instance instMvFunctor_ofCurried_curried [f : MvFunctor F] :
    MvFunctor <| TypeFun.ofCurried <| F.curried :=
  TypeFun.ofCurried_curried_involution ▸ f

instance instQPF_ofCurried_curried [q : MvQPF F] :
    MvQPF <| TypeFun.ofCurried <| F.curried :=
  TypeFun.ofCurried_curried_involution ▸ q

end MvQPF
