
import Lean.Expr
import Lean.Meta
import Lean.Elab.Command
import Lean.Elab.Declaration
import Lean.Elab.DeclModifiers
import Lean.Elab.Inductive
import Lean.Elab.Term

import Qpf.Macro.Data.Internals
-- import Qpf.Macro.Data.MkQpf
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

#check Constructor

section
/-
  A modified version of `elabInductiveViews`
-/
def elabDataView (view : InductiveView) (nlivevars : Nat) : CommandElabM Unit := do
  let ref := view.ref
  let decl ← runTermElabM view.declName fun vars => withRef ref do
    let orig_vars := vars;
    mkDataDecl vars view fun params indFVars decl => do
      if decl.isUnsafe then
        throwError "Unsafe data declarations are not supported"

      dbg_trace "params: {params}"
      dbg_trace "indFVars: {indFVars}"
      dbg_trace "type = {decl.inner.type}"
      dbg_trace "nparams = {decl.nparams}"
      dbg_trace "lparams = {decl.lparams}"

      let ndeadvars := decl.nparams - nlivevars;

      let mut n := ndeadvars;
      let mut deadVars := #[]
      let mut liveVars := #[]


      for var in params do
        if n > 0 then
          deadVars := deadVars.push var
          n := n-1
        else
          liveVars := liveVars.push var

      let liveVarIds := liveVars.map Expr.fvarId!
      let isLiveVar := fun id : FVarId => liveVarIds.contains id

      /-
        Replace all expressions with fresh free vars
      -/
      let mut constraints : List (Expr × Expr) := []
      for ctor in decl.inner.ctors do
        if ctor.type.isForall then      
          constraints := []
          dbg_trace "{ctor.name}: {ctor.type}"
          let (constraints', args) ← 
          forallTelescopeReducing ctor.type fun args type => do
            let mut constraints := constraints
            let mut newArgs : Array Expr := #[]
            for arg in args do
              let newArg ←
                if arg.isFVar && isLiveVar arg.fvarId! then
                  pure arg
                else if let some v := constraints.lookup arg then
                  pure v
                else
                  let v := mkFVar (← mkFreshFVarId);
                  constraints := (arg, v) :: constraints
                  pure v
              newArgs := newArgs.push newArg
            
            pure (constraints, newArgs)
  
          constraints := constraints'
      
      let newVars := constraints.map fun ⟨v, _⟩ => v





      
  
  -- mkQpf decl
end
  


open Macro

-- needed for `view.derivingClasses[0]` to be accpted down below
instance : Inhabited Elab.DerivingClassView := ⟨default, default, default⟩

open Elab.Term in
def elabDataView' (view: InductiveView) : CommandElabM Unit := do
  let ref := view.ref
  let (liveBinders, deadBinders) ← splitLiveAndDeadBinders view.binders.getArgs

  liftTermElabM view.declName <| do
    dbg_trace view.binders
    let (liveBinders, deadBinders) ← splitLiveAndDeadBinders view.binders.getArgs
    dbg_trace "liveVars: {liveBinders}"
    dbg_trace "deadVars: {deadBinders}"

    withAutoBoundImplicit 
    <| elabBinders deadBinders fun deadVars => 
      withLiveBinders liveBinders fun liveVars => 
        withoutAutoBoundImplicit <| do
          for var in liveVars.reverse do
            let type ← inferType var

          -- Check that unsupported features are not used
          let mut ctors : Array CtorView := #[]
          if let some ref := view.type? then
            throwErrorAt ref "Explicitly provided target type is not supported yet. Note that QPFs cannot represent (co)inductive families"

          if view.derivingClasses.size > 0 then
            throwErrorAt view.derivingClasses[0].ref "`deriving` is not supported yet"

          for ctor in view.ctors do
            if !ctor.binders.isNone then
              throwErrorAt ctor.binders "Constructor binders are not supported yet"

          -- elabDataView view 0
                  

    return ()




open Parser.Term in
/-- Top-level elaboration -/
@[commandElab «data»]
def elabData : CommandElab := fun stx => do 
  let modifiers ← elabModifiers stx[0]
  let decl := stx[1]
  let mut view ← inductiveSyntaxToView modifiers decl

  let (liveBinders, deadBinders) ← splitLiveAndDeadBinders view.binders.getArgs
  let newBinders ←
    if liveBinders.size = 0 then
      pure deadBinders
    else
      let liveBinders ← `(bracketedBinder| ( $liveBinders* : Type _ ))
      pure <| deadBinders.push liveBinders
  view := {
    binders := view.binders.setArgs newBinders

    ref             := view.ref            
    declId          := view.declId         
    modifiers       := view.modifiers      
    shortDeclName   := view.shortDeclName  
    declName        := view.declName       
    levelNames      := view.levelNames     
    type?           := view.type?          
    ctors           := view.ctors          
    derivingClasses := view.derivingClasses
  }

  elabDataView view liveBinders.size
  pure ()

end Data.Command


-- set_option trace.Elab.inductive true
variable (A : Type)

inductive Test where
  | test : A → Test

data MyList α where
  | My.nil : MyList α
  | My2.nil :  A → (a : α) → MyList α → MyList α

data MyList α where
  | My.nil : MyList α
  | My2.nil : α → MyList α → MyList α



data QpfList (dead : Type) β γ where
  | nil   : QpfList dead β γ
  | cons  : A → QpfList dead β γ → QpfList dead β γ

data QpfList (A : Type) (dead : Type) β where
  | nil   : QpfList A dead β
  | cons  : A → (dead → β) → QpfList A dead β → QpfList A dead β

-- #check QpfList