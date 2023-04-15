import Qpf

namespace Test

data QpfList α 
  | nil
  | cons : α → QpfList α → QpfList α   

end Test