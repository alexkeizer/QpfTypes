import Qpf

data QpfListWithBinder α 
  | nil
  | cons (hd : α) (tl : QpfListWithBinder α)