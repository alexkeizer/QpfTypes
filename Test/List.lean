import Qpf

namespace Test

data QpfList α 
  | nil
  | cons : α → QpfList α → QpfList α   

#print QpfList.Uncurried
#print QpfList.Base

end Test