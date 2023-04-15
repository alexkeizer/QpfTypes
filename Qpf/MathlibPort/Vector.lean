import Mathlib.Data.Vector

#check Vector.map
#check List.map
#check List.mapM


theorem List.mapM_length  {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} 
                          (f : α → m β) (as : List α) :
    if let pure as := (List.mapM f as) then
      as.length = as.length
    else
      True
  := by
    sorry

def Vector.mapM {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} 
                (f : α → m β) :
      Vector α n → m (Vector β n) 
  | ⟨l, h⟩ => ⟨←List.mapM f l, by simp[*]⟩