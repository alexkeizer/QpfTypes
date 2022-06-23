
import Qpf.Util.TypeVec
import Mathlib

universe u v

/-- A curried function of `n` arguments in `α`, resulting in `β`, i.e., `α → ... → α → β` -/
abbrev CurriedFun (α : Type u) (β : Type v) : Nat → Type (max u v)
  | 0   => PUnit.{u+1} → β
  | 1   => α → β
  | n+1 => α → CurriedFun α β n


/-- A curried type function of `n` arguments, i.e., `Type u → Type u → ... → Type v` -/
abbrev CurriedTypeFun : Nat → Type ((max u v) + 1)
  := CurriedFun (Type u) (Type v)

/-- An uncurried type function, all `n` arguments are collected into a single `TypeVec n` 
    Note that all arguments live in the same universe, but the result may be in a different universe
-/
abbrev TypeFun (n : Nat) : Type ((max u v) + 1) := 
  TypeVec.{u} n → Type v

namespace TypeFun
  def curried : {n : Nat} → TypeFun n → CurriedTypeFun n
    | 0,    F => fun _ => F ![]
    | 1,    F => fun a => F ![a] 
    | n+2,  F => fun a => curried fun αs => F (αs ::: a)

  def ofCurried : {n : Nat} → CurriedTypeFun n → TypeFun n
    | 0,    F, _ => F PUnit.unit
    | 1,    F, α => F (α 0)
    | n+2,  F, α => ofCurried (F α.last) α.drop



  @[simp]
  theorem curried_ofCurried_rfl {F : CurriedTypeFun n} :
    curried (ofCurried F) = F :=
  by    
    cases n
    case zero => simp [curried, ofCurried]
    case succ n => {
      induction n
      <;> simp [curried, ofCurried, Vec.append1]

      case succ _ ih => {
        funext a;
        apply @ih (F a);
      }
    } 



  @[simp]
  theorem ofCurried_curried_rfl {F : TypeFun n} :
    ofCurried (curried F) = F :=
  by    
    cases n
    case zero => 
      funext x; simp [curried, ofCurried]
    case succ n => {
      induction n;
      case zero => {
        funext x;
        simp [curried, ofCurried];
        apply congrArg;
        funext i;
        cases i;
        . simp [Vec.append1, OfNat.ofNat]
        . contradiction
      }

      case succ _ ih => {
        funext x;
        simp [ofCurried, curried];
        let F' := fun α => F (α ::: x.last);
        have : F x = F' x.drop;
        . simp
        rw [this]
        rw [@ih F']
      }
    }
end TypeFun