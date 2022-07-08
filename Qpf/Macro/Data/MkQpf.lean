
import Lean
import Qpf.Macro.Data.DataDecl
import Qpf.Macro.Data.Internals

open Lean
open Elab 
open Meta
open Elab.Term (elabTerm)
open Elab.Command


def Name.replacePrefix (pref new_pref : Name) : Name → Name
  | Name.anonymous => Name.anonymous
  | Name.str p s _ => let p' := if p == pref then new_pref
                                else replacePrefix pref new_pref p
                      Name.mkStr p' s
  | Name.num p v _ => let p' := if p == pref then new_pref
                                else replacePrefix pref new_pref p
                      Name.mkNum p' v

def Name.stripPrefix (pref: Name) : Name → Name
  | Name.anonymous => Name.anonymous
  | Name.str p s _ => if p == pref then Name.mkSimple s
                      else stripPrefix pref p
  | Name.num p v _ => if p == pref then Name.mkNum Name.anonymous v
                      else stripPrefix pref p


/--
  Adds declaration of `.Shape.HeadT`
-/
private def mkHeadT (decl : DataDecl) : CommandElabM Unit := 
do
  let modifiers : Modifiers := {
    isUnsafe := decl.isUnsafe
  }

  let orig_name := decl.inner.name
  let head_t_name := Name.mkStr decl.inner.name "HeadT"
  let ctors := decl.inner.ctors.map fun ctor => { 
    ref := Syntax.missing
    modifiers 
    declName := Name.replacePrefix orig_name head_t_name ctor.name
    binders := mkNullNode
    type? := none
    : CtorView
  } 

  
  let head_t : InductiveView := {
    ref := Syntax.missing
    declId := Syntax.missing
    modifiers := modifiers
    shortDeclName := `HeadT
    declName := head_t_name
    levelNames := []
    binders := mkNullNode
    type? := none
    ctors := ctors.toArray
    derivingClasses := #[]
  }

  elabInductiveViews #[head_t]




/--
  Adds declaration of `.Shape` and `.Shape.Internal`
-/
def mkShape (decl : DataDecl) : CommandElabM Unit := do
  mkHeadT decl


def mkQpf (decl : DataDecl) : CommandElabM Unit := do
  mkShape decl