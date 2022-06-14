
import Qpf.Util.TypeVec
import Mathlib

universe u v

abbrev TypeFun (n : Nat) : Type _ := 
  TypeVec.{u} n → Type v


