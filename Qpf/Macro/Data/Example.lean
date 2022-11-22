import Qpf.Macro.Data

-- set_option trace.Meta.debug true
set_option pp.rawOnError true

data MyList α β where
  | nil : α → β → MyList α β
  | cons : α → MyList α β → MyList α β

def MyList.nil {α β} : α → β → MyList α β :=
  (MvQpf.Fix.mk $ MyList.Shape.nil · ·)

def MyList.cons {α β} : α → MyList α β → MyList α β :=
  (MvQpf.Fix.mk $ MyList.Shape.cons · ·)


-- def MyList.isNil : MyList α β → Bool := MvQpf.Fix.cas



data QpfList α where
  | nil
  | cons : α → QpfList α → QpfList α

data QpfTree α where
  | node : α → QpfList (QpfTree α) → QpfTree α

codata QpfCoTree α where
  | node : α → QpfList (QpfCoTree α) → QpfCoTree α



data QpfTest α β where
  | A : α → α → β → β → QpfTest α β → QpfTree β → QpfCoTree (QpfTree (QpfTest α β)) → QpfTest α β






#print MyList.Internal
#print MyList.Shape
#print MyList.Shape.P

  

data MyList₂ α where
  | My.nil : MyList₂ α
  | My2.nil : α → MyList₂ α

#check MyList₂

#dbg_syntax (a : α) → MyList₂ α → MyList₂ α

data MyList₃ α where
  | My.nil : MyList₃ α
  | My2.nil : α → MyList₃ α → MyList₃ α


-- 
--  Dead variables are not supported yet
--

-- data QpfList₂ (dead : Type) β γ where
--   | nil   : QpfList₂ dead β γ
--   | cons  : QpfList₂ dead β γ → QpfList₂ dead β γ

-- data QpfList (A : Type) (dead : Type) β where
--   | nil   : QpfList A dead β
--   | cons  : A → (dead → β) → QpfList A dead β → QpfList A dead β

#check QpfList

