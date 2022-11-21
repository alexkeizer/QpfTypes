
import Lean.Expr
import Lean.Meta
import Lean.Elab.Command
import Lean.Elab.Declaration
import Lean.Elab.DeclModifiers
import Lean.Elab.Inductive
import Lean.Elab.Term
import Lean.Parser.Term
import Lean.Parser.Command

import Qpf.Macro.Data.Internals
import Qpf.Macro.Data.MkQpf
import Qpf.Macro.Data.Replace
import Qpf.Macro.Data.Count
import Qpf.Macro.Common
import Qpf.Macro.Comp

import Qpf.Qpf.Multivariate.Constructions.Fix

open Lean Meta Elab.Command
open Elab (Modifiers elabModifiers)


namespace Data.Command

/-!
  ## Parser
  for `data` and `codata` declarations
-/
section
  open Lean.Parser Lean.Parser.Command

  def dataDecl : Parser
    := leading_parser "data " >> declId  >> optDeclSig  
                        >> Parser.optional  (symbol " :=" <|> " where") 
                        >> many ctor 
                        >> optDeriving

  def codataDecl : Parser
    := leading_parser "codata " >> declId  >> optDeclSig  
                        >> Parser.optional  (symbol " :=" <|> " where") 
                        >> many ctor 
                        >> optDeriving

  @[commandParser]
  def data : Parser
    := leading_parser declModifiers false >> dataDecl

  @[commandParser]
  def codata : Parser
    := leading_parser declModifiers false >> codataDecl
end

/-!
  ## Elaboration
-/
open Internals
open Elab.Term (TermElabM)

def Name.replacePrefix (pref new_pref : Name) : Name → Name
  | Name.anonymous => Name.anonymous
  | Name.str p s _ => let p' := if p == pref then new_pref
                                else replacePrefix pref new_pref p
                      Name.mkStr p' s
  | Name.num p v _ => let p' := if p == pref then new_pref
                                else replacePrefix pref new_pref p
                      Name.mkNum p' v






def CtorView.declReplacePrefix (pref new_pref : Name) (ctor: CtorView) : CtorView :=
  let declName := Name.replacePrefix pref new_pref ctor.declName
  {
    declName,
    ref := ctor.ref
    modifiers := ctor.modifiers
    binders := ctor.binders
    type? := ctor.type?
  }



open Parser in
def mkHeadT (view : InductiveView) : CommandElabM Name := do
  -- If the original declId was `MyType`, we want to register the head type under `MyType.HeadT`
  let suffix := "HeadT"
  let declName := Name.mkStr view.declName suffix
  let declId := mkNode ``Command.declId #[mkIdent declName, mkNullNode]
  let shortDeclName := Name.mkSimple suffix

  let modifiers : Modifiers := {
    isUnsafe := view.modifiers.isUnsafe
  }
  -- The head type is the same as the original type, but with all constructor arguments removed
  let ctors ← view.ctors.mapM fun ctor => do
    let declName := Name.replacePrefix view.declName declName ctor.declName
    pure { 
      modifiers, declName,
      ref := ctor.ref
      binders := mkNullNode
      type? := none
      : CtorView
    } 

  -- let type ← `(Type $(mkIdent `u))

  -- TODO: make `HeadT` universe polymorphic
  let view := {
    ctors, declId, declName, shortDeclName,
    binders         := view.binders.setArgs #[]
    levelNames      := view.levelNames

    ref             := view.ref            
    modifiers       := view.modifiers      
    type?           := view.type?
    
    derivingClasses := view.derivingClasses
    : InductiveView
  }

  elabInductiveViews #[view]
  pure declName


open Parser in
private def matchAltsOfArray (matchAlts : Array Syntax) : Syntax :=
  mkNode ``Term.matchAlts #[mkNullNode matchAlts]


open Parser in
/--
  Wraps an array of `matchAltExpr` syntax objects into a single `Command.declValEqns` node, for
  use in inductive definitions
-/
private def declValEqnsOfMatchAltArray (matchAlts : Array Syntax) : Syntax :=
  let body := matchAltsOfArray matchAlts
  let body := mkNode ``Term.matchAltsWhereDecls #[body, mkNullNode]
  mkNode ``Command.declValEqns #[body]


open Parser Parser.Term Parser.Command in
def mkChildT (view : InductiveView) (r : Replace) (headTName : Name) : CommandElabM Name := do  
  -- If the original declId was `MyType`, we want to register the child type under `MyType.ChildT`
  let suffix := "ChildT"
  let declName := Name.mkStr view.declName suffix
  let declId := mkNode ``Command.declId #[mkIdent declName, mkNullNode]
  let shortDeclName := Name.mkSimple suffix

  let arity := r.arity
  let target_type := Syntax.mkApp (mkIdent ``TypeVec) #[quote arity]

  let binderIdents := r.getBinderIdents
  let matchAlts ← view.ctors.mapM fun ctor => do  
    let PFin2 := mkIdent ``PFin2
    let head := mkIdent $ Name.replacePrefix view.declName headTName ctor.declName 

    let counts := countVarOccurences r ctor.type?
    let counts := counts.map fun n => Syntax.mkApp PFin2 #[quote n]
    let counts := counts.reverse

    `(matchAltExpr| | $head => (##[ $counts,* ]))

  let body := declValEqnsOfMatchAltArray matchAlts
  let headT := mkIdent headTName

  

  let cmd ← `(
    def $declId : $headT → $target_type
      $body:declValEqns
  )
  elabCommand cmd

  pure declName


-- structure CtorArgs where
--   (all : Array Syntax)
--   (byType : Array (Array Syntax))

-- private def CtorArgs.ofType (acc : CtorArgs) : Syntax → CtorArgs

-- private def CtorArgs.ofCtor (ctor : CtorView) (r : Replace) : CtorArgs :=
--   let acc := ⟨
--     Array.range 
--   ⟩


open Parser.Term in
def mkQpf (shapeView : InductiveView) (headT childT P : Name) (arity : Nat) : CommandElabM Unit := do
  let shape := shapeView.declName
  let qpf_ := mkIdent $ Name.mkStr shape "qpf"

  let P := mkIdent P
  let Shape := mkIdent shape

  let n_ctors := shapeView.ctors.size;

  let box := matchAltsOfArray <|<- shapeView.ctors.mapM fun ctor => do
    `(matchAltExpr| | _ => _)

  let cmd ← `(
    instance $qpf_ : $(mkIdent ``MvQpf) (@$(mkIdent ``TypeFun.ofCurried) $(quote arity) $Shape) := 
      let box   : ∀{α}, $Shape α → $(P).Obj α :=
          fun x => match x with
            $box:matchAlts

      let unbox : ∀{α}, $(P).Obj α → $Shape α := _
      
      $(mkIdent ``MvQpf.ofPolynomial) $P
  )
  elabCommand cmd

  pure ()









structure MkShapeResult where
  (r : Replace)
  (shape : Name)
  (P : Name)

open Parser in
def mkShape (view: InductiveView) : CommandElabM MkShapeResult := do
  -- If the original declId was `MyType`, we want to register the shape type under `MyType.Shape`
  let suffix := "Shape"
  let declName := Name.mkStr view.declName suffix
  let declId := mkNode ``Command.declId #[mkIdent declName, mkNullNode]
  let shortDeclName := Name.mkSimple suffix


  -- Extract the "shape" functors constructors
  let shapeIdent  := mkIdent shortDeclName
  let (ctors, r) ← Replace.run (Replace.shapeOfCtors view.ctors shapeIdent)
  let ctors := ctors.map (CtorView.declReplacePrefix view.declName declName)


  -- Assemble it back together, into the shape inductive type
  let binders ← r.getBinders  
  let view := {
    ctors, declId, declName, shortDeclName,
    binders         := view.binders.setArgs #[binders]
    levelNames      := []

    ref             := view.ref            
    modifiers       := view.modifiers      
    type?           := view.type?          
    
    derivingClasses := view.derivingClasses
  }

  elabInductiveViews #[view]

  let headTName ← mkHeadT view
  let childTName ← mkChildT view r headTName

  let declNameP := Name.mkStr declName "P"
  let u ← `(ident| u) -- use a hygienic id for the universe
  let declIdP := mkNode ``Command.declId #[mkIdent declNameP, mkNullNode 
    -- #[ TODO: make this universe polymorphic
    --   mkAtom ".{",
    --   mkNullNode #[u],
    --   mkAtom "}"
    -- ]
  ]

  let childTId := mkIdent childTName

  elabCommand <|<- `(
    def $declIdP := 
      $(mkIdent ``MvPFunctor.mk):ident.{0} $(mkIdent headTName) $childTId
  )

  pure ⟨r, declName, declNameP⟩




open Parser Macro.Comp in
def mkBase (view : InductiveView) : CommandElabM Syntax := do
  let declId := mkIdent $ Name.mkStr view.declName "Base"
  
  let (view, _) ← makeNonRecursive view;

  let ⟨r, shape, P⟩ ← mkShape view

  let binders := view.binders
  let args := r.expr.toArray

  let target ← `(
    ($(mkIdent ``TypeFun.curried) ($(mkIdent ``MvPFunctor.Obj) $(mkIdent P))) $args*
  )
  dbg_trace "\n{target}\n"
  elabQpfCommand declId binders none target  

  pure declId




def mkAuxConstructions (view : InductiveView) (internal : Syntax) : CommandElabM Unit := do
  let cmd ← `(
    abbrev $(view.declId) := $(mkIdent ``TypeFun.curried) $internal
  )
  elabCommand cmd



/-- Top-level elaboration -/
@[commandElab «data»]
def elabData : CommandElab := fun stx => do 
  let modifiers ← elabModifiers stx[0]
  let decl := stx[1]
  let view ← inductiveSyntaxToView modifiers decl


  let base ← mkBase view

  let internal := mkIdent $ Name.mkStr view.declName "Internal"
  let cmd ← `(
    abbrev $internal := $(mkIdent ``MvQpf.Fix) ($(mkIdent ``TypeFun.ofCurried)  $base)
  ) 
  elabCommand cmd

  mkAuxConstructions view internal
  pure ()

/-- Top-level elaboration -/
@[commandElab «codata»]
def elabCodata : CommandElab := fun stx => do 
  let modifiers ← elabModifiers stx[0]
  let decl := stx[1]
  let view ← inductiveSyntaxToView modifiers decl


  let base ← mkBase view

  let internal := mkIdent $ Name.mkStr view.declName "Internal"
  let cmd ← `(
    abbrev $internal := $(mkIdent ``MvQpf.Cofix) ($(mkIdent ``TypeFun.ofCurried)  $base)
  ) 
  elabCommand cmd

  mkAuxConstructions view internal  
  pure ()

end Data.Command

set_option pp.rawOnError true

data MyList α β where
  | nil : β → MyList α β
  | cons : α → α → MyList α β → MyList α β

data QpfList α where
  | nil
  | cons : α → QpfList α → QpfList α

data QpfTree α where
  | node : α → QpfList (QpfTree α) → QpfTree α

codata QpfCoTree α where
  | node : α → QpfList (QpfCoTree α) → QpfCoTree α

#print QpfCoTree.Internal

def MyList.nil {α β} (b : β) : MyList α β
  := MvQpf.Fix.mk ⟨MyList.Shape.HeadT.nil, fun i j => match i with
      | 0 => match j with 
             | .fz => b
      | 1 => Fin2.elim0 
              (C := fun _ => _)
              $ cast (by simp[Shape.P, Shape.ChildT, Vec.append1]) j
      | 2 => Fin2.elim0 
              (C := fun _ => _)
              $ cast (by simp[Shape.P, Shape.ChildT, Vec.append1]) j
  ⟩

def MyList.cons {α β} (a₁ a₂ : α) (as : MyList α β) : MyList α β
  := MvQpf.Fix.mk ⟨MyList.Shape.HeadT.cons, fun i j => match i with
      | 0 => Fin2.elim0 
              (C := fun _ => _)
              $ cast (by simp[Shape.P, Shape.ChildT, Vec.append1]) j
      | 1 => match j with
             | .fz => a₁
             | .fs .fz => a₂
      | 2 => match j with
             | .fz => as
  ⟩

#check (MvQpf.Fix.mk (F:=TypeFun.ofCurried MyList.Base) (α:=$[Int, Nat]) _ : MyList Nat Int)

#print MyList.Shape
#print MyList.Shape.P


/-
instance instQpfMyListShape : MvQpf (@TypeFun.ofCurried 3 MyList.Shape) := 
  .ofPolynomial MyList.Shape.P (
    fun x => match x with
    | MyList.Shape.nil b_0 b_1 => ⟨MyList.Shape.HeadT.nil, fun i j => (
        by 
          fin_destr i
           <;> simp [MyList.Shape.P, MyList.Shape.ChildT, Vec.append1] at j |-
           <;> try fin_destr j
          
          {
            match j with 
            | 0 => exact b_0
            | 1 => exact b_1
          }
    )⟩
    | MyList.Shape.cons a_0 a_1 => ⟨MyList.Shape.HeadT.cons, fun i j => (
        by 
          simp[TypeVec.drop, Vec.drop, Vec.reverse, Vec.normalize, Vec.append1, 
              TypeVec.last, DVec.last, PFin2.inv, PFin2.weaken] at a_0 a_1
          fin_destr i
           <;> simp [MyList.Shape.P, MyList.Shape.ChildT, Vec.append1] at j |-
           <;> try fin_destr j;
          
          exact a_1;
          exact a_0;
    )⟩
  ) (
    fun ⟨head, child⟩ => match head with
    | MyList.Shape.HeadT.nil  => MyList.Shape.nil (child 0 .fz) (child 0 $ .fs .fz)
    | MyList.Shape.HeadT.cons => MyList.Shape.cons (child 1 .fz) (child 2 .fz)
  ) (by 
      intro _ x;
      rcases x with ⟨head, child⟩;
      cases head
      <;> simp
      <;> apply congrArg
      <;> fin_destr
      <;> rfl          
          
  ) (by 
      intro _ x;
      cases x
      <;> rfl
  )
  
-- #print MyList.Shape.ChildT
-- #check @MyList.cons

#check instQpfMyListShape

-/


-- data MyList α where
--   | My.nil : MyList α
--   | My2.nil :  A → (a : α) → MyList α → MyList α

-- data MyList α where
--   | My.nil : MyList α
--   | My2.nil : α → MyList α → MyList α




-- data QpfList (dead : Type) β γ where
--   | nil   : QpfList dead β γ
--   | cons  : A → QpfList dead β γ → QpfList dead β γ

-- data QpfList (A : Type) (dead : Type) β where
--   | nil   : QpfList A dead β
--   | cons  : A → (dead → β) → QpfList A dead β → QpfList A dead β

-- #check QpfList