/-
  Provides an instance of `MvQPF` for (the uncurried version of) the `List` built-in type
-/

import Qpf.Macro.Data
import Qpf.Qpf.Multivariate.ofPolynomial

namespace MvQPF 
namespace List

  def ListPFunctor : MvPFunctor.{u} 1
    := ⟨ULift Nat, fun n => !![PFin2 n.down]⟩


  abbrev QpfList' := ListPFunctor.Obj
  abbrev List' := @TypeFun.ofCurried 1 List

  abbrev box {Γ} (x : List' Γ) : QpfList' Γ 
    := ⟨
        ULift.up x.length, 
        fun i => cast (by fin_destr i; rfl) $ Vec.ofList x
      ⟩

  abbrev unbox {Γ} (x : QpfList' Γ) : List' Γ 
    := Vec.toList (x.snd 0)
    
  private theorem typeext {α} {f g : α → Sort _} (f_eq_g: f = g) :
    ((a : α) → f a) = ((a : α) → g a) :=
  by
    cases f_eq_g; rfl


  instance : MvQPF List' := 
    .ofIsomorphism _ box unbox (
      by
        intros Γ x;
        rcases x with ⟨⟨n⟩, v⟩
        dsimp[ListPFunctor] at v
        simp [box, unbox];

        apply eq_of_heq;
        apply hcongr
        case H₁ =>
          apply hcongr
          . rfl
          . simp[Vec.toList_length_eq_n]
          . intro _; rfl
          . trivial

        case H₂ =>
          apply heq_funext <;> fin_destr
          . simp[ListPFunctor]
          skip
          simp_heq
          apply HEq.trans (Vec.ofList_toList_iso)
          rfl

        case H₃ => 
          apply typeext;
          fin_destr;

          simp only [ListPFunctor, TypeVec.Arrow, DVec];
          have : List.length (unbox { fst := { down := n }, snd := v }) = n; {
            simp
          }
          simp[this]

        case H₄ => intros; rfl
    ) (
      by 
        intros; apply Vec.toList_ofList_iso;
    )

end List
end MvQPF

#check (inferInstance : MvQPF (@TypeFun.ofCurried 1 List))