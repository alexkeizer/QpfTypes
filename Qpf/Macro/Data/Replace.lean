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

structure CtorArgs where
  (args : Array Name)
  (per_type : Array (Array Name))

structure Replace where
  (expr: Array Syntax)
  (vars: Array Name)
  (ctor: CtorArgs)


private def Replace.new : CommandElabM Replace := 
  do pure ⟨#[], #[], ⟨#[], #[]⟩⟩

private abbrev ReplaceM := StateT Replace CommandElabM

private def CtorArgs.reset : ReplaceM Unit := do
  let r ← StateT.get
  let n := r.vars.size
  let ctor: CtorArgs := ⟨#[], (Array.range n).map fun _ => #[]⟩
  StateT.set ⟨r.expr, r.vars, ctor⟩

private def CtorArgs.get : ReplaceM CtorArgs := do
  pure (←StateT.get).ctor

def Replace.arity (r : Replace) : Nat :=
  r.vars.size

def Replace.getBinderIdents (r : Replace) : Array Syntax :=
  r.vars.map mkIdent

open Parser.Term
def Replace.getBinders (r : Replace) : CommandElabM Syntax := do
  let names := r.getBinderIdents
  `(bracketedBinder| ($names* : Type _ ))








private def ReplaceM.identFor (stx : Syntax) : ReplaceM Syntax := do
  let r ← StateT.get
  let ctor := r.ctor
  let argName ← mkFreshBinderName
  let ctor_args := ctor.args.push argName
  -- dbg_trace "\nstx := {stx}\nr.expr := {r.expr}"

  let name ← match r.expr.indexOf? stx with
  | some id => do      
      let ctor_per_type := ctor.per_type.set! id $ (ctor.per_type.get! id).push argName
      let ctor := ⟨ctor_args, ctor_per_type⟩
      StateT.set ⟨r.expr, r.vars, ctor⟩
      pure $ r.vars.get! id
  | none       => do
      let ctor_per_type := ctor.per_type.push #[argName]
      let name ← mkFreshBinderName
      StateT.set ⟨r.expr.push stx, r.vars.push name, ⟨ctor_args, ctor_per_type⟩⟩
      pure name

  pure $ mkIdent name
  


open Parser in
/--
  Checks that the given type is a sequence of (non-depenedent) arrows, ending in `expected`
-/
private partial def checkResultingType (expected : Syntax) : Syntax → CommandElabM Unit
  | Syntax.node _ ``Term.arrow #[arg, arrow, tail] =>
      checkResultingType expected tail

  | stx@(Syntax.node _ ``Term.arrow _) =>
      throwErrorAt stx "Internal bug: encountered an unexpected form of arrow syntax"

  | stx@(Syntax.node _ ``Term.depArrow _) =>
      throwErrorAt stx "Dependent arrows are not supported, please only use plain arrow types"

  | ctor_type => 
      if ctor_type != expected then
        throwErrorAt ctor_type m!"Unexpected constructor resulting type; expected {expected}, found {ctor_type}"
      else
        pure ()

open Lean.Parser in
/--
  Given a sequence of (non-dependent) arrows, replace each unique expression in between the arrows
  with a fresh variable, such that repeated occurrences of the same expression map to the same
  variable
-/
private partial def shapeOf' : Syntax → ReplaceM Syntax
  | Syntax.node _ ``Term.arrow #[arg, arrow, tail] => do
    let ctor_arg ← ReplaceM.identFor arg
    let ctor_tail ← shapeOf' tail

    -- dbg_trace ">> {arg} ==> {ctor_arg}"    
    pure $ mkNode ``Term.arrow #[ctor_arg, arrow, ctor_tail]

  | ctor_type => 
      pure ctor_type



open Lean.Parser in
/--
  Given a sequence of (non-dependent) arrows, change the last expression into `res_type`
-/
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

#eval toString ((Array.range 0).map (fun _ => (#[] : Array Nat)))

/--
  Extract the constructors for a "shape" functor from the original constructors.
  It replaces all constructor arguments with fresh variables, ensuring that repeated occurences
  of the same type map to a single variable, where "same" refers to a very simple notion of
  syntactic equality. E.g., it does not realize `Nat` and `ℕ` are the same.
-/
def Replace.shapeOfCtors (view : InductiveView) 
                          (shapeIdent : Syntax) 
                          : ReplaceM (Array CtorView × Array CtorArgs) := do  
  let ctors := view.ctors

  let pairs ← ctors.mapM fun ctor => do
    if !ctor.binders.isNone then
      throwErrorAt ctor.binders "Constructor binders are not supported yet, please provide all arguments in the type"

    dbg_trace "{ctor.declName}: {ctor.type?}"

    CtorArgs.reset

    let type? ← ctor.type?.mapM $ shapeOf'

    pure $ (CtorView.withType? ctor type?, ←CtorArgs.get)

  let r ← StateT.get
  let ctors := pairs.map Prod.fst;
  let ctorArgs := pairs.map fun ⟨_, ctorArgs⟩ =>
      let per_type := ctorArgs.per_type
      
      let diff := r.vars.size - ctorArgs.per_type.size

      -- HACK: It seems that `Array.append` causes a stack overflow, so we go through `List` for now
      -- TODO: fix this after updating to newer Lean version
      let per_type := per_type.appendList $ (List.range diff).map (fun _ => (#[] : Array Name));
      ⟨ctorArgs.args, per_type⟩

  -- Now that we know how many free variables were introduced, we can fix up the resulting type
  -- of each constructor to be `Shape α_0 α_1 ... α_n`
  let r ← StateT.get
  let res := Syntax.mkApp shapeIdent r.getBinderIdents

  let ctors ← ctors.mapM fun ctor => do
    let type? ← ctor.type?.mapM (setResultingType res) 
    pure $ CtorView.withType? ctor type?

  pure (ctors, ctorArgs)



/-- Runs the given action with a fresh instance of `Replace` -/
def Replace.run : ReplaceM α → CommandElabM (α × Replace) := 
  fun x => do 
    let r ← Replace.new
    StateT.run x r


private partial def replaceStx (find replace : Syntax) : Syntax → Syntax := fun stx =>
  if stx == find then
    replace
  else
    stx.setArgs (stx.getArgs.map (replaceStx find replace))




open Parser
/--
  Makes a type spefication non-recursive, by replacing all recursive occurences by a fresh bound variable.
-/
def makeNonRecursive (view : InductiveView) : CommandElabM (InductiveView × Name) := do
  let expected := Syntax.mkApp (mkIdent view.shortDeclName) (
    (Macro.getBinderIdents view.binders.getArgs)
  )  

  let rec ← mkFreshBinderName
  let recId := mkIdent rec

  let newBinder := mkNode ``Term.simpleBinder #[mkNullNode #[recId], mkNullNode]
  let binders := view.binders
  let binders := binders.setArgs (binders.getArgs.push newBinder)

  let ctors ← view.ctors.mapM fun ctor => do
    pure $ CtorView.withType? ctor $ ← ctor.type?.mapM (fun type => do
      checkResultingType expected type
      pure $ replaceStx expected recId type
    )

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