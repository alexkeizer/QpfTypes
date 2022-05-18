
import Qpf.Util.TypeVec
import Mathlib

universe u

/-- A curried function of exactly `n` arguments -/
abbrev CurriedFun (α β : Type u) : Nat → Type u
  | 0   => β
  | n+1 => α → CurriedFun α β n


/-- A curried type function of `n` arguments, i.e., `Type u → Type u → ... → Type u` -/
abbrev CurriedTypeFun : Nat → Type (u+1)
  := CurriedFun (Type u) (Type u)


/-- A partly curried type function, so `Type u → ... → Type u → TypeVec j → Type u` 
    The `n` curried arguments are considered "dead", while the `m` uncurried arguments are live.
    When `F : GenTypeFun` is a functor, the live variables are those in which `F` is functorial, 
    whereas `F` is not necessarily functorial in the dead arguments.
-/
abbrev GenTypeFun (n m : Nat) : Type _
  := CurriedFun (Type u) (TypeVec.{u} m → Type u) n


/-- An uncurried type function, all `n` arguments are collected into a single `TypeVec n` -/
abbrev TypeFun : Nat → Type _
  := GenTypeFun 0



unif_hint (n : Nat) where
  |- TypeFun.{u} n =?= TypeVec.{u} n → Type (u)


namespace TypeFun
  def ofCurried {n : Nat} (F : CurriedTypeFun n) : TypeFun n
    := fun α => match n with
        | 0   => F
        | n+1 => ofCurried (F α.hd) (Vec.tl α)

  /--
    Killing a variable means to turn it from "live" into "dead", hence it turns from an uncurried
    argument into a curried argument
  -/
  def kill {n : Nat} (i : Fin2 (n+1)) (F : TypeFun (n+1)) : Type _ → TypeFun n
    := fun τ α => F (α.insertAt τ i)

  abbrev kill_first {n : Nat} := @kill n 0
end TypeFun

namespace GenTypeFun 
  def kill : {n m : Nat} →  (i : Fin2 (m+1)) →  (F : GenTypeFun n (m+1)) →  GenTypeFun (n+1) m
    | 0  , _, i, F => TypeFun.kill i F
    | n+1, _, i, F => fun τ => kill i (F τ)

  abbrev kill_first {n m : Nat} := @kill n m 0

  def asCurriedLeft  {m : Nat} (F : GenTypeFun 0 m) : CurriedTypeFun m
    := match m with
        | 0   => F TypeVec.nil
        | m+1 => fun τ => asCurriedLeft (kill_first F τ)

  def asCurriedRight {n : Nat} (F : GenTypeFun n 0) : CurriedTypeFun n
    := match n with
        | 0   => F TypeVec.nil
        | n+1 => fun τ => asCurriedRight (F τ)

  def asCurried {n m : Nat} (F : GenTypeFun n m) : CurriedTypeFun (m + n)
    := match n with
        | 0   => F.asCurriedLeft
        | n+1 => match m with
                  | 0 => cast (by simp) F.asCurriedRight
                  | _ => fun τ => asCurried (n:=n) (F τ)
end GenTypeFun



