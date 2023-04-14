import Qpf

-- set_option trace.Meta.debug true
-- set_option trace.Elab.inductive true
sudo set_option trace.QPF true
set_option pp.rawOnError true
set_option pp.analyze true
set_option pp.universes true


data QpfList α : Type 2 where 
  | nil : QpfList α
  | cons : α → QpfList α → QpfList α



-- #check TypeFun.ofCurried QpfList.Shape

#synth MvQPF.IsPolynomial <| MvQPF.Fix <| @TypeFun.ofCurried 2 QpfList.Shape

#check QpfList

#check @MvQPF.Fix.drec _ QpfList.Uncurried _

#exit

namespace QpfList
  #print QpfList.nil
  #print QpfList.cons


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

  #print List.recOn

  #check @List.rec
  #check @QpfList.rec

  

  theorem nil_neq_cons (a : α) (as : QpfList α) : @QpfList.nil α ≠ QpfList.cons a as := 
    by
      simp[nil, cons]
      intro contra
      sorry
      -- contradiction

  #print nil_neq_cons
end QpfList










data QpfTree α where
  | node : α → List (QpfTree α) → QpfTree α

codata QpfCoTree α where
  | node : α → List (QpfCoTree α) → QpfCoTree α



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













#print QpfList.Uncurried
#print QpfList.Shape
#print QpfList.Shape.P

  

data QpfList₂ α where
  | My.nil : QpfList₂ α
  | My2.nil : α → QpfList₂ α

#check QpfList₂

data QpfList₃ α where
  | My.nil : QpfList₃ α
  | My2.nil : α → QpfList₃ α → QpfList₃ α



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


/-
  # Composition pipeline
-/

qpf P₁ α β := α
qpf P₂ α β := β

qpf C₁ α β := Nat
qpf C₂ (n : Nat) α β := PFin2 n

qpf G₄ α β ρ := QpfList ρ


/-
  # Dead variables
-/

data Arrow (α : Type _) β
  | mk : (α → β) → Arrow α β

codata FinAlt {n : Nat} β
  | mk : PFin2 n → FinAlt β

#print FinAlt.mk


data QpfList₄ (dead : Type) β γ where
  | nil   : QpfList₄ dead β γ
  | cons  : QpfList₄ dead β γ → QpfList₄ dead β γ



/-
  # Regression tests

  These cases failed at some point, include them here as a regression test
-/

data PairOf α β
  | mk : α → β → β → PairOf α β

data QpfTest α β where
  | A : α → α → β → QpfTest α β → QpfTree β → QpfCoTree (QpfTree (QpfTest α β)) → QpfTest α β

data RepAfterConst β
  | mk : Nat →  β → β → RepAfterConst β

codata NatList α where
  | nil : NatList α
  | cons : Nat → NatList α → NatList α

data QpfList₅ (A : Type) (dead : Type) β where
  | nil   : QpfList₅ A dead β
  | cons  : A → (dead → β) → QpfList₅ A dead β → QpfList₅ A dead β