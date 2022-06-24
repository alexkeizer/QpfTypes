import Qpf.Qpf.Multivariate.Basic


abbrev ToMvQpf {n} (F : CurriedTypeFun n) 
  := MvQpf (TypeFun.ofCurried F)


namespace MvQpf

  instance instCurriedOfCurried {F : TypeFun n} [q : MvQpf F] :
    MvQpf (TypeFun.ofCurried F.curried) :=
  cast (
    by simp only [TypeFun.ofCurried_curried_involution]
  ) q
    
end MvQpf