import Qpf.Qpf.Multivariate.Basic

import Qpf.Qpf.Multivariate.Constructions.Fix
import Qpf.Qpf.Multivariate.Constructions.Comp
import Qpf.Qpf.Multivariate.Constructions.Prj

import Qpf.Qpf.Multivariate.Constructions.Permute.Qpf
import Qpf.Qpf.Multivariate.Constructions.Merge.Qpf

set_option pp.rawOnError true

open MvQpf

-- inductive QpfList (α : Type)
--   | nil
--   | cons : α → QpfList α → QpfList α
namespace QpfList
  inductive HeadT
    | nil
    | cons

  abbrev ChildT : HeadT → TypeVec 2
    | HeadT.nil , _ => Empty
    | HeadT.cons, _ => Unit

  abbrev P := MvPFunctor.mk HeadT ChildT

  instance qpf_P : MvQpf P.Obj := 
    by infer_instance


  abbrev QpfList' 
    := Fix QpfList.P.Obj

  def QpfList (α : Type) 
    := QpfList' (fun _ => α)

  
  instance qpf : MvQpf QpfList' := 
    by infer_instance


  @[matchPattern]
  def nil {α : Type} : QpfList α :=
    Fix.mk ⟨HeadT.nil, fun _ emp => by contradiction⟩

  @[matchPattern]
  def cons {α} (hd : α) (tl : QpfList α) : QpfList α :=
    Fix.mk ⟨HeadT.cons, fun i _ => match i with
                          | Fin2.fz   => tl
                          | Fin2.fs _ => hd
    ⟩

  def one_two_three : QpfList Nat :=
    cons 1 $ cons 2 $ cons 3 $ nil

  /-
    Pattern matching does not work like one would expect, but we'll ignore it for now

  def mul2 : QpfList Nat → QpfList Nat
    | nil        => nil
    | cons hd tl => cons (2*hd) (mul2 tl)
  -/


  -- def rec {α} 
  --         {motive : QpfList α → Sort _} 
  --         : (motive nil) 
  --         → ((hd : α) → (tl : QpfList α) → motive (cons hd tl))
  --         → (t : QpfList α) 
  --         → motive t := 
  -- fun base_case rec_case t => by
  --   let t' := Fix.dest t;
  --   simp [MvPFunctor.Obj] at t'
  --   rcases t' with ⟨a, f⟩
  --   cases a <;> simp [MvPFunctor.B] at f
    
    
    -- let g := fun ⟨a, f⟩ => match a with
    --   | HeadT.nil  => cast (
    --                     by  delta nil;
    --                         apply congrArg; apply congrArg;
    --                         simp [MvFunctor.map];
    --                         conv in (fun x emp => _) => {
    --                           tactic => funext x y; contradiction;
    --                         }                             
    --                   ) base_case
    --   | HeadT.cons => by simp [MvPFunctor.B, HeadT, ChildT] at f
    --                      skip
    --                      sorry
                      -- cast (
                      --   _
                      -- ) (rec_case (f (Fin2.fz) (by simp [P.B])) _)
    -- Fix.drec (β := motive) g t

  
end QpfList
open QpfList (QpfList)







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



#check QpfList.QpfList'


-- inductive QpfTree (α : Type)
--   | leaf
--   | node : α → QpfTree α → QpfList (QpfTree α) → QpfTree α
namespace QpfTree

  /-
    First, the shape functor

    inductive QpfTree.Shape (α β γ : Type)
    | leaf
    | node : α → β → γ → QpfTree.Shape α β γ
  -/
  namespace Shape
    inductive HeadT
      | leaf
      | node

    abbrev ChildT : HeadT → TypeVec 3
      | HeadT.leaf, _ => Empty
      | HeadT.node, 0 => Unit
      | HeadT.node, 1 => Unit
      | HeadT.node, 2 => Unit

    abbrev P := MvPFunctor.mk HeadT ChildT
  end Shape

  def Proj {n : Nat} (i : Fin2 n) := MvPFunctor.mk Unit (fun _ (j : Fin2 n) => Unit)

  abbrev comp_G : Fin2 3 → TypeFun 2
      | 0 => MvQpf.Prj 0
      | 1 => MvQpf.Prj 1
      | 2 => MvQpf.Comp QpfList.QpfList' (fun _ => @MvQpf.Prj 2 1)

  example : VecMvFunctor comp_G :=
    by infer_instance

  abbrev P_Obj := Shape.P.Obj

  abbrev F : TypeFun 2
    := MvQpf.Comp P_Obj comp_G
    

  example : MvFunctor F :=
    by infer_instance

  set_option pp.explicit true
  example : MvQpf F :=
    by
      unfold F
      -- apply MvQpf.Comp.instQpf (G := comp_G) (F := P_Obj) (fF := _) (fG := ?_) (q' := ?_)
      -- infer_instance
      sorry


  -- #check ( : MvFunctor F)
  -- #check (MvQpf.Comp.instQpf : MvQpf F)

  -- abbrev QpfTree (α : Type) 
  --   := Fix F (fun _ => α)

  
end QpfTree


