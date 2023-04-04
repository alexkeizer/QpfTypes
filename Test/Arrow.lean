import Qpf

set_option trace.QPF true
set_option pp.analyze true
set_option pp.raw true

#check MvQPF.Arrow _

data Arrow (α : Type _) β
  | mk : (α → β) → Arrow α β


#print Arrow.Shape
#print Arrow.Base
