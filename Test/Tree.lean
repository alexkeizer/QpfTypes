import Qpf
set_option trace.QPF true

-- set_option pp.all true
set_option pp.rawOnError true


data QpfTree α where
  | node : α → List (QpfTree α) → QpfTree α