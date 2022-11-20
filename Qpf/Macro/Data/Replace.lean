import Lean.Meta
import Lean.Parser.Term
import Lean.Elab.Command

import Qpf.Macro.Common

open Lean Meta Elab.Command

/-
  This file contains the core "shape" extraction logic.

  It establishes the `Replace` struct, and corresponding `ReplaceM` state monad, which are used
  to replace all expressions in a type with fresh variables.

-/

structure Replace where
  (expr: List Syntax)
  (vars: List Name)

def Replace.new : Replace := ⟨[], []⟩

private abbrev ReplaceM := StateT Replace CommandElabM

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
      let id := r.expr.length
      let name := Name.mkSimple ("α_" ++ toString id)
      --TODO collision check with dead binders, once added
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
def Replace.shapeOfCtors (shapeIdent: Syntax) (ctors : Array CtorView) : ReplaceM (Array CtorView) := do
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
  fun x => StateT.run x Replace.new