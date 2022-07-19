
import Qpf.Qpf.Multivariate.Basic

namespace MvQpf 

  def ArrowPFunctor (x : Type u) : MvPFunctor.{u} 1
    := ⟨PUnit, fun _ => ![x]⟩

  def Arrow' (x : Type _) : TypeFun 1
    := (ArrowPFunctor x).Obj

  /--
    A constructor for arrow types `x → y`, which is functorial in `y`
  -/
  abbrev Arrow : CurriedTypeFun 2
    := fun x => (Arrow' x).curried


  instance : MvQpf (Arrow' x) :=
    by unfold Arrow'; infer_instance

  instance : MvQpf (TypeFun.ofCurried (Arrow x)) 
    := inferInstance


  namespace Arrow 
    def box (f : α → β) : (Arrow α β)
      := ⟨(), fun | 0 => f⟩

    def unbox : Arrow α β → α → β
      | ⟨_, f⟩ => f 0

    theorem box_unbox_id :
      box (unbox f) = f :=
    by
      simp[box, unbox]
      apply congrArg
      funext i;
      cases i;
      . rfl
      . contradiction

    theorem unbox_box_id :
      unbox (box f) = f :=
    by
      rfl
  end Arrow

end MvQpf