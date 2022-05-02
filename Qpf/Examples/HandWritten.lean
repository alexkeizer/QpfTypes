import Qpf.Qpf.Multivariate.Basic
import Qpf.Qpf.Multivariate.Constructions.Fix
import Qpf.Qpf.Multivariate.Constructions.Comp

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
  --          let a := f 1 ()
  --          simp [TypeVec.append1, Vec.cons] at a;
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



-- inductive QpfTree (α : Type)
--   | nil
--   | cons : α → QpfList (QpfTree α) → QpfList α
namespace QpfTree
  namespace Base
    inductive HeadT
      | nil
      | cons

    abbrev ChildT : HeadT → TypeVec 3
      | HeadT.nil, _ => Empty
      | HeadT.cons, 0 => Unit
      | HeadT.cons, 1 => Unit
      | HeadT.cons, 2 => Empty

    abbrev P := MvPFunctor.mk HeadT ChildT
  end Base

  def Id {n : Nat} := MvPFunctor.mk Unit (fun _ (_ : Fin2 n) => Unit)

  #check MvQpf.Comp Base.P.Obj
  abbrev Base'.P 
    := MvQpf.Comp Base.P.Obj (fun i => match i with
        | 0 => Id.Obj
        | 1 => QpfList.QpfList'
        | 2 => Id.Obj
    )
  
end QpfTree


