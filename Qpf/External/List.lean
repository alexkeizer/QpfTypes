/-
  Provides an instance of `MvQpf` for (the uncurried version of) the `List` built-in type
-/

import Qpf.Macro.Data
import Qpf.Qpf.Multivariate.ofPolynomial

namespace Qpf 
namespace List

  data QpfList α
  | nil  : QpfList α
  | cons : α → QpfList α → QpfList α


end List
end Qpf