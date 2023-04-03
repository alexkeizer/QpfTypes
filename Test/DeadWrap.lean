import Qpf

namespace Test
  data DeadWrap (α : Type) β
    | mk : α → DeadWrap α β

  #check DeadWrap.Shape
  #check DeadWrap.Base
  #check DeadWrap.Uncurried

  #check DeadWrap.mk

end Test