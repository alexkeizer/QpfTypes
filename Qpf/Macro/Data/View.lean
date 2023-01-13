import Lean
import Qpf.Macro.Common

open Lean
open Meta Elab Elab.Command 



inductive DataCommand where
  | Data
  | Codata
  deriving BEq, Inhabited

def DataCommand.fromSyntax : Syntax → CommandElabM DataCommand
  | Syntax.atom _ "data"   => pure .Data
  | Syntax.atom _ "codata" => pure .Codata
  | stx => throwErrorAt stx "Expected either `data` or `codata`"



/-
  Mostly a replication of `InductiveView`, but for `data`/`codata`
  The `binders` field is replaced by `liveBinders`/`deadBindders`
-/
structure DataView where
  ref             : Syntax
  declId          : Syntax
  modifiers       : Modifiers
  shortDeclName   : Name
  declName        : Name
  levelNames      : List Name
  binders         : Syntax
  type?           : Option Syntax
  ctors           : Array CtorView
  derivingClasses : Array DerivingClassView
  -- further elements are changed from inductiveView
  command         : DataCommand
  liveBinders     : Array Syntax
  deadBinders     : Array Syntax
    deriving Inhabited





def DataView.asInductive (view : DataView) : InductiveView
  := {
    ref             := view.ref
    declId          := view.declId
    modifiers       := view.modifiers      
    shortDeclName   := view.shortDeclName  
    declName        := view.declName       
    levelNames      := view.levelNames     
    binders         := view.binders        
    type?           := view.type?          
    ctors           := view.ctors          
    derivingClasses := view.derivingClasses
  }


open Lean.Parser in
def DataView.pushLiveBinder (view : DataView) (binderIdent : Syntax) : DataView
  :=  let liveBinders := view.liveBinders.push binderIdent
      let newBinder := mkNode ``Term.simpleBinder #[mkNullNode #[binderIdent], mkNullNode]
      let binders := view.binders
      let binders := binders.setArgs (binders.getArgs.push newBinder)
      {
        liveBinders, binders,

        ref             := view.ref
        declId          := view.declId
        modifiers       := view.modifiers      
        shortDeclName   := view.shortDeclName  
        declName        := view.declName       
        levelNames      := view.levelNames     
        type?           := view.type?          
        ctors           := view.ctors          
        derivingClasses := view.derivingClasses
        command         := view.command
        deadBinders     := view.deadBinders
      }


def DataView.setCtors (view : DataView) (ctors : Array CtorView) : DataView
  := {
        ctors,

        ref             := view.ref
        declId          := view.declId
        modifiers       := view.modifiers      
        shortDeclName   := view.shortDeclName  
        declName        := view.declName       
        levelNames      := view.levelNames     
        binders         := view.binders     
        type?           := view.type?          
        derivingClasses := view.derivingClasses
        command         := view.command
        liveBinders     := view.liveBinders
        deadBinders     := view.deadBinders
      }







/-
  # Parsing syntax into a view
-/


/--
  Raises (hopefully) more informative errors when `data` or `codata` are used with unsupported
  specifications
-/
def sanityChecks (view : DataView) : CommandElabM Unit := do  
  if view.liveBinders.isEmpty then    
    if view.deadBinders.isEmpty then
      if view.command == .Codata then
        throwError "Due to a bug, codatatype without any parameters don't quite work yet. Please try adding parameters to your type"
      else 
        throwError "Trying to define a data without variables, you probably want an `inductive` type instead"
    else
      throwErrorAt view.binders "You should mark some variables as live by removing the type ascription (they will be automatically inferred as `Type _`), or if you don't have variables of type `Type _`, you probably want an `inductive` type"

  -- TODO: remove once dead variables are fully supported
  if !view.deadBinders.isEmpty then
    dbg_trace "Dead variables are not fully supported yet"


  -- TODO: make this more intelligent. In particular, allow types like `Type`, `Type 3`, or `Type u`
  --       and only throw an error if the user tries to define a family of types
  match view.type? with
  | some t => throwErrorAt t "Unexpected type; type will be automatically inferred. Note that inductive families are not supported due to inherent limitations of QPFs"
  | none => pure ()



/-
  Heavily based on `inductiveSyntaxToView` from Lean.Elab.Declaration
-/
def dataSyntaxToView (modifiers : Modifiers) (decl : Syntax) : CommandElabM DataView := do
  -- `data`/`codata` declarations may be noncomputable (not sure about partial, but we allow it for now)
  -- checkValidInductiveModifier modifiers

  let (binders, type?) := expandOptDeclSig decl[2]
  let declId           := decl[1]
  let ⟨name, declName, levelNames⟩ ← expandDeclId declId modifiers
  addDeclarationRanges declName decl
  let ctors      ← decl[4].getArgs.mapM fun ctor => withRef ctor do
    -- def ctor := leading_parser " | " >> declModifiers >> ident >> optDeclSig
    let ctorModifiers ← elabModifiers ctor[1]
    if ctorModifiers.isPrivate && modifiers.isPrivate then
      throwError "invalid 'private' constructor in a 'private' inductive datatype"
    if ctorModifiers.isProtected && modifiers.isPrivate then
      throwError "invalid 'protected' constructor in a 'private' inductive datatype"
    checkValidCtorModifier ctorModifiers
    let ctorName := ctor.getIdAt 2
    let ctorName := declName ++ ctorName
    let ctorName ← withRef ctor[2] $ applyVisibility ctorModifiers.visibility ctorName
    let (binders, type?) := expandOptDeclSig ctor[3]
    addDocString' ctorName ctorModifiers.docString?
    addAuxDeclarationRanges ctorName ctor ctor[2]
    return { ref := ctor, modifiers := ctorModifiers, declName := ctorName, binders := binders, type? := type? : CtorView }
  let classes ← getOptDerivingClasses decl[5]


  let command ← DataCommand.fromSyntax decl[0]
  let (liveBinders, deadBinders) ← Macro.splitLiveAndDeadBinders binders.getArgs


  let view := {
    ref             := decl
    shortDeclName   := name
    derivingClasses := classes
    declId, modifiers, declName, levelNames
    binders, type?, ctors,
    command, liveBinders, deadBinders,
  }
  sanityChecks view
  return view
