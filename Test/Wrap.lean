import Qpf

namespace Test
  data Wrap α 
    | mk : α → Wrap α

  #check Test.Wrap.mk
  #check (Wrap.Shape : CurriedTypeFun 2)

end Test