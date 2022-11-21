import Lean.Meta
import Lean.Parser.Term
import Lean.Elab.Command

import Qpf.Macro.Common

open Lean Meta Elab.Command Elab.Term

/-
  This file contains the core "shape" extraction logic.

  It establishes the `Replace` struct, and corresponding `ReplaceM` state monad, which are used
  to replace all expressions in a type with fresh variables.

-/

structure Replace where
  (expr: List Syntax)
  (vars: List Name)

private def Replace.new : CommandElabM Replace := 
  do pure ⟨[], []⟩

private abbrev ReplaceM := StateT Replace CommandElabM

def Replace.arity (r : Replace) : Nat :=
  r.vars.length

def Replace.getBinderIdents (r : Replace) : Array Syntax :=
  (r.vars.map mkIdent).toArray

open Parser.Term
def Replace.getBinders (r : Replace) : CommandElabM Syntax := do
  let names := r.getBinderIdents
  `(bracketedBinder| ($names* : Type _ ))


private def List.indexOf? [BEq α] : α → List α → Option Nat 
  | _, []     =>  none
  | a, b::bs  =>  if a == b then 
                    some 0
                  else
                    (indexOf? a bs).map (· + 1)

private def ReplaceM.identFor (stx : Syntax) : ReplaceM Syntax := do
  let r ← StateT.get
  -- dbg_trace "\nstx := {stx}\nr.expr := {r.expr}"

  let name ← match List.indexOf? stx r.expr with
  | some id => do
      pure $ r.vars.get! id
  | none       => do
      let name ← mkFreshBinderName
      StateT.set ⟨stx :: r.expr, name :: r.vars⟩
      pure name

  pure $ mkIdent name
  

open Lean.Parser in
private partial def shapeOf' : Syntax → ReplaceM Syntax
  | Syntax.node _ ``Term.arrow #[arg, arrow, tail] => do
    let ctor_arg ← ReplaceM.identFor arg
    let ctor_tail ← shapeOf' tail

    -- dbg_trace ">> {arg} ==> {ctor_arg}"    
    pure $ mkNode ``Term.arrow #[ctor_arg, arrow, ctor_tail]
  | ctor_type => 
      pure ctor_type



open Lean.Parser in
private partial def setResultingType (res_type : Syntax) : Syntax → ReplaceM Syntax
  | Syntax.node _ ``Term.arrow #[arg, arrow, tail] => do
    let tail ← setResultingType res_type tail
    pure $ mkNode ``Term.arrow #[arg, arrow, tail]
  | ctor_type => 
      pure res_type


def CtorView.withType? (ctor : CtorView) (type? : Option Syntax) : CtorView := {
  ref       := ctor.ref
  modifiers := ctor.modifiers
  declName  := ctor.declName
  binders   := ctor.binders
  type?     := type?
}

/-
  TODO: currently these functions ignore dead variables, everything is replaced.
  This is OK, we can supply a "dead" value to a live variable, but we lose the ability to have
  dead variables live in a different universe from live ones (since the shape functor will require
  all its arguments to live in the same universe).

  We should instead detect which expressions are dead, and NOT introduce fresh variables for them.
  Instead, have the shape functor also take the same dead binders as the original.
  This does mean that we should check for collisions between the original dead binders, and the 
  fresh variables.
-/

/--
  Extract the constructors for a "shape" functor from the original constructors.
  It replaces all constructor arguments with fresh variables, ensuring that repeated occurences
  of the same type map to a single variable, where "same" refers to a very simple notion of
  syntactic equality. E.g., it does not realize `Nat` and `ℕ` are the same.
-/
def Replace.shapeOfCtors (ctors : Array CtorView) (shapeIdent : Syntax) : ReplaceM (Array CtorView) := do
  let ctors ← ctors.mapM fun ctor => do
    if !ctor.binders.isNone then
      throwErrorAt ctor.binders "Constructor binders are not supported yet, please provide all arguments in the type"

    dbg_trace "{ctor.declName}: {ctor.type?}"

    let type? ← ctor.type?.mapM shapeOf'

    pure $ CtorView.withType? ctor type?

  -- Now that we know how many free variables were introduced, we can fix up the resulting type
  -- of each constructor to be `Shape α_0 α_1 ... α_n`
  let r ← StateT.get
  let res := Syntax.mkApp shapeIdent r.getBinderIdents

  ctors.mapM fun ctor => do
    let type? ← ctor.type?.mapM (setResultingType res) 
    pure $ CtorView.withType? ctor type?
  -- pure ctors


/-- Runs the given action with a fresh instance of `Replace` -/
def Replace.run : ReplaceM α → CommandElabM (α × Replace) := 
  fun x => do 
    let r ← Replace.new
    StateT.run x r


#check Syntax.getArgs
#check Syntax.setArgs

private partial def replaceStx (find replace : Syntax) : Syntax → Syntax := fun stx =>
  if stx == find then
    replace
  else
    stx.setArgs (stx.getArgs.map (replaceStx find replace))


open Parser
/--
  Makes a type non-recursive, by replacing all recursive occurences by a fresh bound variable.
-/
def makeNonRecursive (view : InductiveView) : CommandElabM (InductiveView × Name) := do
  let rec ← mkFreshBinderName
  let recId := mkIdent rec

  let newBinder := mkNode ``Term.simpleBinder #[mkNullNode #[recId], mkNullNode]
  let binders := view.binders
  let binders := binders.setArgs (binders.getArgs.push newBinder)

  let origArgs := Macro.getBinderIdents view.binders.getArgs
  let orig     := Syntax.mkApp (mkIdent view.shortDeclName) origArgs

  let ctors := view.ctors.map fun ctor =>
    CtorView.withType? ctor $ ctor.type?.map (replaceStx orig recId)

  pure ({
    binders, ctors,

    ref             := view.ref             
    declId          := view.declId          
    modifiers       := view.modifiers       
    shortDeclName   := view.shortDeclName   
    declName        := view.declName        
    levelNames      := view.levelNames      
    type?           := view.type?           
    derivingClasses := view.derivingClasses 
  }, rec)