
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

def elabDataView' (view: InductiveView) : CommandElabM Unit := do
  let ref := view.ref
  liftTermElabM view.declName <| do
    dbg_trace view.binders
    let (liveVars, deadVars) ← splitLiveAndDeadBinders view.binders.getArgs
    dbg_trace "liveVars: {liveVars}"
    dbg_trace "deadVars: {deadVars}"

    return ()



/-- Top-level elaboration -/
@[commandElab «data»]
def elabData : CommandElab := fun stx => do 
  let modifiers ← elabModifiers stx[0]
  let decl := stx[1]
  let view ← inductiveSyntaxToView modifiers decl
  elabDataView view
  pure ()

end Data.Command