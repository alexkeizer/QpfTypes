import Qpf

/-!
Tests to assert we can have (`co`)`data` types without
any live variables
-/

namespace Qpf.Test.NoLiveVars

data Data (α : Type) where
  | dat : α → Data α

codata Codata (α : Type) where
  | dat : α → Codata α → Codata α
