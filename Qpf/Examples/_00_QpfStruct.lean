import Qpf

open MvQpf



-- inductive QpfStruct (α : Type) where
--   mk : α → QpfStruct α

namespace QpfStruct

  abbrev HeadT  := Unit

  @[simp]
  abbrev ChildT : HeadT → TypeVec 2
    := fun _ i => match i with 
        | 0 => Empty 
        | 1 => Unit

  abbrev P := MvPFunctor.mk HeadT ChildT

  abbrev QpfStruct (α : Type)
    := Fix P.Obj (fun _ => α)

  abbrev mk {α : Type} (a : α) : QpfStruct α
    := Fix.mk ⟨(), fun i _ => match i with  
                                | 0 => by contradiction
                                | 1 => a
    ⟩

  -- def rec {α} 
  --         {motive : QpfStruct α → Sort _} 
  --         : ((a : α) → motive (mk a))
  --         → (t : QpfStruct α)
  --         → motive t := 
  --   fun recurse t =>
  --     let g := fun ⟨a, f⟩ =>
  --       by cases a
  --          let a := f 1(a₁, ..., aₘ).append1, Vec.cons] at a;
  --          apply recurse a
  --     Fix.drec (β := motive) g t

  abbrev rec {α motive} := Fix.drec (F:=P.Obj) (α := α) (β := motive)

  -- open MvPFunctor in
  -- example : QpfStruct α → α :=
  --   by intro x
  --      let x := Fix.dest x;
  --      simp [Obj, TypeVec.append1] at x;
  --      cases x
  --     --  have : ∃ a f, x = Fix.mk ⟨a, f⟩
  --     --   := by unfold QpfStruct
           
  --      cases x using QpfStruct.rec
    
end QpfStruct

open QpfStruct (QpfStruct)