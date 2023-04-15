import Qpf
import Test.Tree
import Test.CoTree



data QpfList₂ α where
  | My.nil : QpfList₂ α
  | My2.nil : α → QpfList₂ α

data QpfList₃ α where
  | My.nil : QpfList₃ α
  | My2.nil : α → QpfList₃ α → QpfList₃ α


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