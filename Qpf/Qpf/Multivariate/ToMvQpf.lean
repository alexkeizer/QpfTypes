import Qpf.Qpf.Multivariate.Basic


class ToMvQpf {n} (F : CurriedTypeFun n) where
  q : MvQpf (TypeFun.ofCurried F)


namespace MvQpf

  instance instCurriedOfCurried {F : TypeFun n} [q : MvQpf F] :
    MvQpf (TypeFun.ofCurried F.curried) :=
  cast (
    by simp only [TypeFun.ofCurried_curried_involution]
  ) q
    
end MvQpf

namespace ToMvQpf

  instance instCurried {F : TypeFun n} [q : MvQpf F] : 
    ToMvQpf F.curried := 
  ⟨MvQpf.instCurriedOfCurried⟩  

end ToMvQpf