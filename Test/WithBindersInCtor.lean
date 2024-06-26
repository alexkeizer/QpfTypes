import Qpf.Macro.Data

data QpfListWithBinder α
  | cons (h : α) (tl : QpfListWithBinder α)
  | nil

data Wrap α
  | mk : α → Wrap α
data Wrap₂ α
  | mk (a : α) : Wrap₂ α
data Wrap₃ α
  | mk (a : α)

