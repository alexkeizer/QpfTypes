
def rewrite {α β : Sort u} (heq : α = β) (a : α) : β
  := Eq.rec (motive := λ χ _ => χ) a heq 

def rewrite_cong {α : Sort u} {a b : α} {f : α → Sort v} (heq : a = b) (fa : f a) : f b
  := let hfeq : f a = f b := congrArg f heq
     rewrite hfeq fa