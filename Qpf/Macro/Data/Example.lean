
import Qpf.Macro.Data
import Mathlib

set_option trace.Meta.debug true
set_option pp.rawOnError true


data MyList (α β : Type _) where
  | Nil  : MyList α β
  | Cons : {a : α} → β → (as : MyList α β) → MyList α β

#check MyList.HeadT
#check MyList.HeadT.Nil
#print MyList.HeadT 


-- data Tree' (α β : Type 2) : Type _
--   | Nil  : Tree' α β
--   | Node : (a : α) → (β → Tree' α β) → Tree' α β

-- #print Tree'.HeadT

-- #print MyList
-- #print MyList'

inductive Tree (α : Type)
  | nil
  | node : α → Tree α → Tree α → Tree α

def MyContainer :  Bool → Type → Type 
  | true  => List
  | false => Tree

inductive Test (α : Type)
  | mk : {b : Bool} → MyContainer b α → Test α 