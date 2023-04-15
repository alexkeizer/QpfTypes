import Qpf


codata QpfCoTree α where
  | node : α → List (QpfCoTree α) → QpfCoTree α