import Qpf

variable (α : Type)

inductive WithVariable' β 
  | mk : α → β → WithVariable' β

data WithVariable β 
  | mk : α → β → WithVariable β