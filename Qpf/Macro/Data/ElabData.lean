
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
                        -- >> optDeriving

  @[commandParser]
  def data : Parser
    := leading_parser declModifiers false >> dataDecl
end

/-!
  ## Elaboration
-/
open Internals

section
/-
  A modified version of `elabInductiveViews`
-/
def elabDataView (view : InductiveView) : CommandElabM Unit := do
  let ref := view.ref
  let decl ← runTermElabM view.declName fun vars => withRef ref do
    let decl ← mkDataDecl vars view
    trace[Meta.debug] "vars = {vars}"
    trace[Meta.debug] "type = {decl.inner.type}"
    trace[Meta.debug] "nparams = {decl.nparams}"
    trace[Meta.debug] "lparams = {decl.lparams}"
    if decl.isUnsafe then
      throwError "Unsafe data declarations are not supported"      
    pure decl
  
  -- mkQpf decl
end
  


open Macro

-- needed for `view.derivingClasses[0]` to be accpted down below
instance : Inhabited Elab.DerivingClassView := ⟨default, default, default⟩

open Elab.Term in
def elabDataView' (view: InductiveView) : CommandElabM Unit := do
  let ref := view.ref
  liftTermElabM view.declName <| do
    dbg_trace view.binders
    let (liveBinders, deadBinders) ← splitLiveAndDeadBinders view.binders.getArgs
    dbg_trace "liveVars: {liveBinders}"
    dbg_trace "deadVars: {deadBinders}"

    withAutoBoundImplicit 
    <| elabBinders deadBinders fun deadVars => 
      withLiveBinders liveBinders fun liveVars => 
        withoutAutoBoundImplicit <| do

          -- let mut type := mkForall
          for var in liveVars.reverse do
            let type ← inferType var


          let mut ctors : Array CtorView := #[]
          if let some ref := view.type? then
            throwErrorAt ref "Explicitly provided target type is not supported yet. Note that QPFs cannot represent (co)inductive families"

          if view.derivingClasses.size > 0 then
            throwErrorAt view.derivingClasses[0].ref "`deriving` is not supported yet"

          for ctor in view.ctors do
            if !ctor.binders.isNone then
              throwErrorAt ctor.binders "Constructor binders are not supported yet"

            -- let type ← Internals.elabCtors
            
      -- else
        

    return ()



/-- Top-level elaboration -/
@[commandElab «data»]
def elabData : CommandElab := fun stx => do 
  let modifiers ← elabModifiers stx[0]
  let decl := stx[1]
  let view ← inductiveSyntaxToView modifiers decl
  elabDataView' view
  pure ()

end Data.Command


data QpfList (ded : Nat) α β where
  | nil   : QpfList α β
  | cons  : α → β → QpfList α β