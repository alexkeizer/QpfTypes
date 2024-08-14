
import Lean
import Qpf.Macro.Common
import Qpf.Macro.ParserUtils

open Lean
open Meta Elab Elab.Command 

open Parser.Term (bracketedBinder)
open Parser.Command (declId)


inductive DataDefCommand where
  | DDef
  | CoDDef
  deriving DecidableEq, Inhabited, Repr

namespace DataDefCommand 

def fromSyntax : Syntax → CommandElabM DataDefCommand
  | Syntax.atom _ "ddef"   => pure DDef
  | Syntax.atom _ "codef" => pure CoDDef
  | stx => throwErrorAt stx "Expected either `ddef` or `codef`"

instance : ToString DataDefCommand where
  toString := fun
    | DDef => "data"
    | CoDDef => "codata"

end DataDefCommand

deriving instance Repr for AttributeKind
deriving instance Repr for Attribute
deriving instance Repr for RecKind
deriving instance Repr for Visibility
deriving instance Repr for Modifiers
deriving instance Repr for Term.BinderView

structure BView where
  name : Lean.Name

  ref  : TSyntax ``Parser.Term.bracketedBinder -- TODO: This is incorrect and should be corrected
  id   : Ident
  type : Term
  bi   : BinderInfo
deriving Repr

open private toBinderViews from Lean.Elab.Binders in
def BView.fromStx (stx : Syntax) : TermElabM (Array BView) :=
  (·.map fun {ref, id, type, bi} =>
    let type := ⟨type⟩
    let ref  := ⟨ref⟩
    let id   := ⟨id⟩

    let name := id.getId

    {
      name
      ref
      id
      type
      bi
    }
  ) <$> toBinderViews stx

def BView.toStx [Monad m] [MonadQuotation m] (bview : BView) : m $ TSyntax ``Parser.Term.bracketedBinder := do match bview.bi with
  | .default        => `(bb|($(bview.id) : $(bview.type)))
  | .implicit       => `(bb|{$(bview.id) : $(bview.type)})
  | .strictImplicit => `(bb|⦃$(bview.id) : $(bview.type)⦄)
  | .instImplicit   => `(bb|[$(bview.id) : $(bview.type)])

structure DataDefView where
  kind          : DataDefCommand
  ref           : Syntax

  modifiers     : Modifiers
  declId        : Syntax

  shortDeclName : Name
  declName      : Name
  levelNames    : List Name

  binders       : Array BView
  type?         : Option Term
  value         : Syntax

  deriving Inhabited, Repr

def ddefSyntaxToView (modifiers : Modifiers) (decl : Syntax) : CommandElabM DataDefView := do 
  let (binders, type?) := expandOptDeclSig decl[2]

  let declId  : TSyntax ``declId := ⟨decl[1]⟩
  let ⟨shortDeclName, declName, levelNames⟩ ← expandDeclId declId modifiers

  let command ← DataDefCommand.fromSyntax decl[0]

  let binders ← match binders with
    | .node _ _ args => liftTermElabM (args.mapM fun x => BView.fromStx x)
    | s => throwErrorAt s "expected binders"
  let binders := binders.flatten

  return {
    kind := command
    ref := decl

    modifiers

    declId

    shortDeclName
    declName
    levelNames

    binders
    type? := type?.map (⟨·⟩)
    value := decl[3]
  }
