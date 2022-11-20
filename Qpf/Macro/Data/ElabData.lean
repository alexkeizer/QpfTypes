
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

open Lean Meta Elab.Command
open Elab (Modifiers elabModifiers)


namespace Data.Command

/-!
  ## Parser
  for `data` declarations
-/
section
  open Lean.Parser Lean.Parser.Command

  def dataDecl : Parser
    := leading_parser "data " >> declId  >> optDeclSig  
                        >> Parser.optional  (symbol " :=" <|> " where") 
                        >> many ctor 
                        >> optDeriving

  @[commandParser]
  def data : Parser
    := leading_parser declModifiers false >> dataDecl
end

/-!
  ## Elaboration
-/
open Internals
open Elab.Term (TermElabM)

section



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

  let view := {
    ctors, declId, declName, shortDeclName,
    binders         := view.binders.setArgs #[]
    levelNames      := []

    ref             := view.ref            
    modifiers       := view.modifiers      
    type?           := view.type?          
    
    derivingClasses := view.derivingClasses
    : InductiveView
  }

  elabInductiveViews #[view]
  pure declName

#check Array
#check List.range

open Parser Parser.Term Parser.Command in
def mkChildT (view : InductiveView) (r : Replace) (headTName : Name) : CommandElabM Name := do  
  -- If the original declId was `MyType`, we want to register the child type under `MyType.ChildT`
  let suffix := "ChildT"
  let declName := Name.mkStr view.declName suffix
  let declId := mkNode ``Command.declId #[mkIdent declName, mkNullNode]
  let shortDeclName := Name.mkSimple suffix

  let arity := r.expr.length
  let target_type := Syntax.mkApp (mkIdent ``TypeVec) #[quote arity]

  let binderIdents := r.getBinderIdents
  let matchAlts ← view.ctors.mapM fun ctor => do  
    let PFin2 := mkIdent ``PFin2
    let head := mkIdent $ Name.replacePrefix view.declName headTName ctor.declName 

    let counts := countVarOccurences r ctor.type?
    let counts := counts.map fun n => Syntax.mkApp PFin2 #[quote n]

    `(matchAltExpr| | $head => (##[ $counts,* ]))

  -- Wrap the match arms in the appropriate syntax category, so it can be used in a `def` command
  let body := mkNode ``Term.matchAlts #[mkNullNode matchAlts]
  let body := mkNode ``Term.matchAltsWhereDecls #[body, mkNullNode]
  let body := mkNode ``Command.declValEqns #[body]

  let headT := mkIdent headTName

  

  let cmd ← `(
    def $declId : $headT → $target_type
      $body:declValEqns
  )
  dbg_trace "{cmd}"
  elabCommand cmd

  pure declName



open Parser in
def mkShape (view: InductiveView) : CommandElabM Unit := do
  -- If the original declId was `MyType`, we want to register the shape type under `MyType.Shape`
  let suffix := "Shape"
  let declName := Name.mkStr view.declName suffix
  let declId := mkNode ``Command.declId #[mkIdent declName, mkNullNode]
  let shortDeclName := Name.mkSimple suffix

  let headT := mkIdent $ Name.mkStr view.declName "HeadT"


  -- Extract the "shape" functors constructors
  let (ctors, r) ← Replace.run (Replace.shapeOfCtors (mkIdent shortDeclName) view.ctors)
  let ctors := ctors.map (CtorView.declReplacePrefix view.declName declName)


  -- Assemble it back together, into the shape functor
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

  elabCommand <|<- `(
    def $(mkIdent $ Name.mkStr declName "P") := 
      $(mkIdent ``MvPFunctor.mk) $(mkIdent headTName) $(mkIdent childTName)
  )

  








open Parser.Term Parser in
/-- Top-level elaboration -/
@[commandElab «data»]
def elabData : CommandElab := fun stx => do 
  let modifiers ← elabModifiers stx[0]
  let decl := stx[1]
  let mut view ← inductiveSyntaxToView modifiers decl

  -- let (liveBinders, deadBinders) ← splitLiveAndDeadBinders view.binders.getArgs
  -- dbg_trace "liveBinders: {liveBinders}"def MyList.Shape.ChildT : MyList.Shape.HeadT → Nat
--   | MyList.Shape.HeadT.nil  => 1
--   | MyList.Shape.HeadT.cons => 1
  -- let newBinders ←
  --   if liveBinders.size = 0 then
  --     pure deadBinders
  --   else
  --     let liveBinders ← `(bracketedBinder| ( $liveBinders* : Type _ ))
  --     pure <| deadBinders.push liveBinders

  mkShape view
  pure ()

end
end Data.Command




data MyList α β where
  | nil : β → β → MyList α β
  | cons : α → MyList α β → MyList α β

#print MyList.Shape
#print MyList.Shape.ChildT

#check TypeFun.ofCurried

-- instance instQpfMyListShape : MvQpf (@TypeFun.ofCurried 3 MyList.Shape) := 
--   .ofPolynomial MyList.Shape.P (
--     fun x => match x with
--     | MyList.Shape.nil => _ -- ⟨MyList.Shape.HeadT.nil, fun i y => by cases i <;> simp[MvPFunctor.B, MyList.Shape.P]⟩
--     | MyList.Shape.cons .. => _
--   ) _ _ _
  
-- #print MyList.Shape.ChildT
-- #check @MyList.cons

#check PFin2
#check TypeVec.append1

-- def ChildT : MyList.Shape.HeadT → TypeVec 3
--   | MyList.Shape.HeadT.nil  => $[PFin2 0, PFin2 1, PFin2 0]
--   | MyList.Shape.HeadT.cons => $[PFin2 1, PFin2 0, PFin2 1]

-- def MyList.Shape.ChildT : MyList.Shape.HeadT → Nat
--   | MyList.Shape.HeadT.nil  => 1
--   | MyList.Shape.HeadT.cons => 1

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