import Qpf

set_option trace.QPF true

data Arrow (α : Type) β
  | mk : α → Arrow α β

-- data Arrow (α : Type _) β
--   | mk : (α → β) → Arrow α β