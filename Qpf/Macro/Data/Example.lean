import Qpf.Macro.Data
import Qpf.Qpf.Multivariate.Constructions.Quot

-- set_option trace.Meta.debug true
set_option pp.rawOnError true

data MyList α where
  | nil : MyList α
  | cons : α → MyList α → MyList α

data QpfList α where
  | nil
  | cons : α → QpfList α → QpfList α

data QpfTree α where
  | node : α → QpfList (QpfTree α) → QpfTree α

codata QpfCoTree α where
  | node : α → QpfList (QpfCoTree α) → QpfCoTree α



/-- If `a ∈ as`, return `as` with (a single occurence of) `a` removed.
    Otherwise, if `a ∉ as`, return `none` -/
def List.is_rem (a : α) : List α → List α → Prop
  | b::bs, c::cs  =>    (a = c  ∧ bs = c::cs)
                      ∨ (b = c  ∧ bs.is_rem a cs)
  | _, _          => false

/-- Equates lists up-to permutation -/
def List.perm ⦃α⦄ : MyList.Internal α → MyList.Internal α → Prop
  -- body omitted
  := by sorry
  -- | [],    []  =>  true
  -- | a::as, bs  =>  ∃cs : List α, cs.is_rem a bs ∧ as.perm cs
  -- | _, _       =>  false
                      

abbrev MultiSet.Internal := MvQpf.Quot1 List.perm
abbrev MultiSet := TypeFun.curried MultiSet.Internal

noncomputable instance : MvQpf MultiSet.Internal := MvQpf.relQuot List.perm (by sorry)

#check (inferInstance : MvQpf MultiSet.Internal)

-- data UnorderedTree α where
--   | node : α → MultiSet (UnorderedTree α) → UnorderedTree α


#print MyList



-- TODO: find out why the following won't work
-- codata NatList α where
--   | nil : NatList α
--   | cons : Nat → NatList α → NatList α



def MyList.nil {α} : MyList α :=
  MvQpf.Fix.mk MyList.Shape.nil

def MyList.cons {α} : α → MyList α → MyList α :=
  fun a as => MvQpf.Fix.mk (MyList.Shape.cons a as)


def MyList.isNil : MyList α → Bool := 
  MvQpf.Fix.rec fun as => match as with
    | .nil => true
    | _    => false

def MyList.isCons : MyList α → Bool := 
  fun as => match as.dest with
    | .cons .. => true
    | _        => false

def MyList.length : MyList α → Nat :=
  MvQpf.Fix.rec fun as => match as with
    | .nil                => 0
    | .cons a (as : Nat)  => as + 1 


inductive MyListInd α
 | nil
 | cons : α → MyListInd α → MyListInd α

 #check @MyListInd.casesOn
 #check @MyListInd.recOn
 #check @MyListInd.rec
 #check MyListInd.noConfusion (α:=Nat)


codata QpfStream α where
  | mk : α → QpfStream α → QpfStream α

def QpfStream.mk : α → QpfStream α → QpfStream α :=
  fun a as => MvQpf.Cofix.mk (Shape.mk a as)


/-- The stream `0,0,0,...` -/
def QpfStream.zeroes : QpfStream Nat :=
  MvQpf.Cofix.corec (fun _ => 
    Shape.mk (0 : Nat) ()
  ) ()

/-- The stream `0,1,2,3,4,...` -/
def QpfStream.naturals : QpfStream Nat :=
  MvQpf.Cofix.corec (fun (i : Nat) => 
    Shape.mk (i : Nat) (i + 1 : Nat)
  ) 0


/-- Add two streams together -/
def QpfStream.add (as bs : QpfStream Nat) : QpfStream Nat :=
    MvQpf.Cofix.corec (fun ⟨as, bs⟩ => 
      let ⟨(a : Nat), as⟩ := MvQpf.Cofix.dest as;
      let ⟨(b : Nat), bs⟩ := MvQpf.Cofix.dest bs;
      Shape.mk (a + b : Nat) (as, bs)
    ) (as, bs)


-- data MyListPair α β where
--   | nil_nil
--   | cons_nil  : α → MyListPair α β
--   | nil_cons  : β → MyListPair α β
--   | cons_cons : α → β → MyListPair α β

-- def MyListPair.of (as : MyList α) (bs : MyList β) : MyListPair α β










-- data QpfTest α β where
--   | A : α → α → β → β → QpfTest α β → QpfTree β → QpfCoTree (QpfTree (QpfTest α β)) → QpfTest α β






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


namespace Quotient
  data List' α
  | nil 
  | cons : α → List' α → List' α

  #print List'

  def List'.perm ⦃α⦄: Quotient.List'.Internal α → Quotient.List'.Internal α → Prop
    := by sorry

  abbrev Multiset' : TypeFun 1 := MvQpf.Quot1 List'.perm
  abbrev Multiset  := Multiset'.curried

  noncomputable instance : MvQpf Multiset' := 
    MvQpf.relQuot _ (
      by
        intros
        sorry
    )


  noncomputable data Foo α where
    | node : α → Multiset (Foo α) → Foo α
end Quotient

