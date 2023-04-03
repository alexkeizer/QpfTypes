import Qpf

namespace Test
  data Wrap α 
    | mk : α → Wrap α

  #check Wrap.Shape
  #check Wrap.Base
  #check Wrap.Uncurried

  #check Wrap.mk
  #check (Wrap.Shape : CurriedTypeFun 2)

end Test