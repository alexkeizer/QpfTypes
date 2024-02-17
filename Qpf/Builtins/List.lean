/-
  Provides an instance of `MvQPF` for (the uncurried version of) the `List` built-in type
-/

import Qpf.Macro.Data
import Qpf.Qpf.Multivariate.ofPolynomial
import Qpf.Util

namespace MvQPF 
namespace List

  def ListPFunctor : MvPFunctor.{u} 1
    := ⟨ULift Nat, fun n => !![PFin2 n.down]⟩


  abbrev QpfList' := ListPFunctor.Obj
  abbrev List' := @TypeFun.ofCurried 1 List

  abbrev box {Γ} (x : List' Γ) : QpfList' Γ 
    := ⟨
        ULift.up x.length, 
        fun .fz j => Vec.ofList x (PFin2.toFin2 j)
      ⟩

  abbrev unbox {Γ} (x : QpfList' Γ) : List' Γ 
    := Vec.toList fun i => x.snd 0 (PFin2.ofFin2 i)
    
  private theorem typeext {α} {f g : α → Sort _} (f_eq_g: f = g) :
    ((a : α) → f a) = ((a : α) → g a) :=
  by
    cases f_eq_g; rfl


  instance funcInst : MvFunctor List' :=
    MvFunctor.ofIsomorphism _ box unbox

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
          apply HEq.funext <;> fin_destr
          . simp[ListPFunctor]
          apply HEq.trans Vec.ofList_toList_iso'
          simp only [Eq.ndrec, id_eq, eq_mpr_eq_cast, PFin2.toFin2_ofFin2_iso]
          apply HEq.trans cast_fun_arg
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
        intros _ x;
        induction x
        . rfl
        . {
          simp only [Vec.ofList, Vec.toList]
          congr
        }
    )
    funcInst
    (by simp[funcInst, MvFunctor.ofIsomorphism])

end List
end MvQPF

#check (inferInstance : MvQPF (@TypeFun.ofCurried 1 List))
