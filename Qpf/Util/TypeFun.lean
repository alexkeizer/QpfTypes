
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
  def reverseArgs : TypeFun n → TypeFun n :=
    fun v α => v (α.reverse)

  @[simp]
  theorem reverseArgs_involution (F : TypeFun n) :
    F.reverseArgs.reverseArgs = F :=
  by
    simp only [reverseArgs, Vec.reverse_involution]


  def curriedAux : {n : Nat} → TypeFun n → CurriedTypeFun n
    | 0,    F => fun _ => F ![]
    | 1,    F => fun a => F ![a] 
    | n+2,  F => fun a => curriedAux fun αs => F (αs ::: a)

  def curried (F : TypeFun n) : CurriedTypeFun n
    := curriedAux (F.reverseArgs)


  def ofCurriedAux : {n : Nat} → CurriedTypeFun n → TypeFun n
    | 0,    F, _ => F PUnit.unit
    | 1,    F, α => F (α 0)
    | n+2,  F, α => ofCurriedAux (F α.last) α.drop

  def ofCurried (F : CurriedTypeFun n) : TypeFun n
    := (ofCurriedAux F).reverseArgs



  @[simp]
  theorem curriedAux_ofCurriedAux_involution {F : CurriedTypeFun n} :
    curriedAux (ofCurriedAux F) = F :=
  by    
    cases n
    case zero => simp [curriedAux, ofCurriedAux]
    case succ n => {
      induction n
      <;> simp [curriedAux, ofCurriedAux, Vec.append1]

      case succ _ ih => {
        funext a;
        simp[reverseArgs_involution]
        apply @ih (F a);
      }
    } 

  @[simp]
  theorem curried_ofCurried_involution {F : CurriedTypeFun n} :
    curried (ofCurried F) = F :=
  by    
    simp only [curried, ofCurried, reverseArgs_involution]
    apply curriedAux_ofCurriedAux_involution



  @[simp]
  theorem ofCurriedAux_curriedAux_involution {F : TypeFun n} :
    ofCurriedAux (curriedAux F) = F :=
  by    
    cases n
    case zero => 
      funext x; simp [curriedAux, ofCurriedAux]
    case succ n => {
      induction n;
      case zero => {
        funext x;
        simp [curriedAux, ofCurriedAux];
        apply congrArg;
        funext i;
        cases i;
        . simp [Vec.append1, OfNat.ofNat]
        . contradiction
      }

      case succ _ ih => {
        funext x;
        simp [ofCurriedAux, curriedAux];
        let F' := fun α => F (α ::: x.last);
        have : F x = F' x.drop;
        . simp
        rw [this]
        rw [@ih F']
      }
    }

  @[simp]
  theorem ofCurried_curried_involution {F : TypeFun n} :
    ofCurried (curried F) = F :=
  by    
    simp only [ofCurried, curried, ofCurriedAux_curriedAux_involution]
    apply reverseArgs_involution
end TypeFun