import Lean

open Lean Meta Core
open Lean.Elab.Command (InductiveView)
open Lean.Elab.Term (TermElabM)


structure DataType extends InductiveType where
  deriving Inhabited

/--
  `DataDecl` is a recreation of `Declaration.inductDecl`, meant for the `data` command
-/
structure DataDecl where
  (lparams  : List Name) 
  (nparams  : Nat) 
  (inner    : DataType)
  (view     : InductiveView)
  (isUnsafe : Bool)
  deriving Inhabited


def DataDecl.asInductDecl (self : DataDecl) : Declaration :=
  Declaration.inductDecl self.lparams self.nparams [self.inner.toInductiveType] self.isUnsafe
