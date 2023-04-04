import Qpf

set_option trace.QPF true

namespace Test
  data DeadWrap (α : Type) β
    | mk : α → DeadWrap α β

  #check DeadWrap.Shape
  #check DeadWrap.Base
  #check DeadWrap.Uncurried

  #print DeadWrap.Shape
  #print axioms DeadWrap.Base
  #print DeadWrap.Base

  #check DeadWrap.mk
  #print DeadWrap.mk

end Test