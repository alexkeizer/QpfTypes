import Qpf

set_option trace.QPF true
set_option pp.rawOnError true

data QpfList α where
  | nil : QpfList α
  | cons : α → QpfList α → QpfList α

namespace QpfList
  def rec {α : Type _} {motive : QpfList α → Sort _} :
    motive QpfList.nil 
    → ((head : α) → (tail : QpfList α) → motive tail → motive (QpfList.cons head tail))
    → (t : QpfList α) 
    → motive t
  :=
    fun nil cons => MvQPF.Fix.drec (fun x => 
      match x with
      | .nil            => nil
      | .cons head tail => cons head tail.fst tail.snd
    )

  @[reducible] protected def recOn {α : Type _} {motive : QpfList α → Sort _} :
      (t : QpfList α) 
      → motive QpfList.nil 
      → ((head : α) → (tail : QpfList α) → motive tail → motive (QpfList.cons head tail)) 
      → motive t 
    :=
      fun t nil cons => QpfList.rec nil cons t
end QpfList






/-- If `a ∈ as`, return `as` with (a single occurrence of) `a` removed.
    Otherwise, if `a ∉ as`, return `none` -/
def List.is_rem (a : α) : List α → List α → Prop
  | b::bs, c::cs  =>    (a = c  ∧ bs = c::cs)
                      ∨ (b = c  ∧ bs.is_rem a cs)
  | _, _          => false

/-- Equates lists up-to permutation -/
def List.perm ⦃α⦄ : QpfList.Uncurried α → QpfList.Uncurried α → Prop
  -- body omitted
  := by sorry
  -- | [],    []  =>  true
  -- | a::as, bs  =>  ∃cs : List α, cs.is_rem a bs ∧ as.perm cs
  -- | _, _       =>  false
                      

abbrev MultiSet.Uncurried := MvQPF.Quot1 List.perm
abbrev MultiSet := TypeFun.curried MultiSet.Uncurried

noncomputable instance : MvQPF MultiSet.Uncurried := MvQPF.relQuot List.perm (by sorry)

#check (inferInstance : MvQPF MultiSet.Uncurried)

-- data UnorderedTree α where
--   | node : α → MultiSet (UnorderedTree α) → UnorderedTree α


#print QpfList


def QpfList.isNil : QpfList α → Bool := 
  MvQPF.Fix.rec fun as => match as with
    | .nil => true
    | _    => false

def QpfList.isCons : QpfList α → Bool := 
  fun as => match as.dest with
    | .cons .. => true
    | _        => false

def QpfList.length : QpfList α → Nat :=
  MvQPF.Fix.rec fun as => match as with
    | .nil                => 0
    | .cons a (as : Nat)  => as + 1 



inductive QpfListInd α
  | nil
  | cons : α → QpfListInd α → QpfListInd α

 #check @QpfListInd.casesOn
 #check @QpfListInd.recOn
 #check @QpfListInd.rec
 #check QpfListInd.noConfusion (α:=Nat)


codata QpfStream α where
  | mk : α → QpfStream α → QpfStream α

#print QpfStream.mk


/-- The stream `0,0,0,...` -/
def QpfStream.zeroes : QpfStream Nat :=
  MvQPF.Cofix.corec (fun _ => 
    Shape.mk (0 : Nat) ()
  ) ()

/-- The stream `0,1,2,3,4,...` -/
def QpfStream.naturals : QpfStream Nat :=
  MvQPF.Cofix.corec (fun (i : Nat) => 
    Shape.mk (i : Nat) (i + 1 : Nat)
  ) 0


/-- Add two streams together -/
def QpfStream.add (as bs : QpfStream Nat) : QpfStream Nat :=
    MvQPF.Cofix.corec (fun ⟨as, bs⟩ => 
      let ⟨(a : Nat), as⟩ := MvQPF.Cofix.dest as;
      let ⟨(b : Nat), bs⟩ := MvQPF.Cofix.dest bs;
      Shape.mk (a + b : Nat) (as, bs)
    ) (as, bs)


-- data QpfListPair α β where
--   | nil_nil
--   | cons_nil  : α → QpfListPair α β
--   | nil_cons  : β → QpfListPair α β
--   | cons_cons : α → β → QpfListPair α β

-- def QpfListPair.of (as : QpfList α) (bs : QpfList β) : QpfListPair α β











#check QpfList


namespace Quotient
  data List' α
  | nil 
  | cons : α → List' α → List' α

  #print List'

  def List'.perm ⦃α⦄: Quotient.List'.Uncurried α → Quotient.List'.Uncurried α → Prop
    := by sorry

  abbrev Multiset' : TypeFun 1 := MvQPF.Quot1 List'.perm
  abbrev Multiset  := Multiset'.curried

  noncomputable instance : MvQPF Multiset' := 
    MvQPF.relQuot _ (
      by
        intros
        sorry
    )


  -- noncomputable data Foo α where
  --   | node : α → Multiset (Foo α) → Foo α

  -- #print Foo
  -- #print Quotient.Foo.node



  def List.perm : List α → List α → Prop
    := by sorry

  def NativeMultiset α := Quot.mk (@List.perm α)
end Quotient







