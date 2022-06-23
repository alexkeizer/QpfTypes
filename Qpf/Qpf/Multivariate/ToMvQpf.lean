import Qpf.Qpf.Multivariate.Basic


class ToMvQpf {n} (F : CurriedTypeFun n) where
  q : MvQpf (TypeFun.ofCurried F)


namespace ToMvQpf

  instance instCurried {F : TypeFun n} [q : MvQpf F] : 
    ToMvQpf F.curried :=
  by
    constructor
    apply cast ?_ q
    apply congrArg
    apply Eq.symm
    apply TypeFun.ofCurried_curried_involution
  

end ToMvQpf