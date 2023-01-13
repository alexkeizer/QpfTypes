import Lean.Expr
import Lean.Meta
import Lean.Elab.Command
import Lean.Elab.Declaration
import Lean.Elab.DeclModifiers
import Lean.Elab.Inductive
import Lean.Elab.Term
import Lean.Parser.Term
import Lean.Parser.Command

import Qpf.Macro.Data.Internals
import Qpf.Macro.Data.Replace
import Qpf.Macro.Data.Count
import Qpf.Macro.Data.View
import Qpf.Macro.Common
import Qpf.Macro.Comp

import Qpf.Qpf.Multivariate.Constructions.Fix

open Lean Meta Elab.Command
open Elab (Modifiers elabModifiers)

private def Array.enum (as : Array α) : Array (Nat × α) :=
  (Array.range as.size).zip as


/--
  Given a natural number `n`, produce a sequence of `n` calls of `.fs`, ending in `.fz`.

  The result corresponds to a `i : PFin2 _` such that `i.toNat == n`
-/
private def PFin2.quoteOfNat : Nat → Syntax
  | 0   => mkIdent ``PFin2.fz
  | n+1 => Syntax.mkApp (mkIdent ``PFin2.fs) #[(quoteOfNat n)]


namespace Data.Command

/-!
  ## Parser
  for `data` and `codata` declarations
-/
section
  open Lean.Parser Lean.Parser.Command

  def inductive_like (cmd : String) : Parser
    := leading_parser cmd >> declId  >> optDeclSig  
                        >> Parser.optional  (symbol " :=" <|> " where") 
                        >> many ctor 
                        >> optDeriving

  def data := inductive_like "data "
  def codata := inductive_like "codata "

  @[commandParser]
  def declaration : Parser
    := leading_parser declModifiers false >> (data <|> codata)
end

/-!
  ## Elaboration
-/
open Internals
open Elab.Term (TermElabM)

def Name.replacePrefix (pref new_pref : Name) : Name → Name
  | Name.anonymous => Name.anonymous
  | Name.str p s _ => let p' := if p == pref then new_pref
                                else replacePrefix pref new_pref p
                      Name.mkStr p' s
  | Name.num p v _ => let p' := if p == pref then new_pref
                                else replacePrefix pref new_pref p
                      Name.mkNum p' v






def CtorView.declReplacePrefix (pref new_pref : Name) (ctor: CtorView) : CtorView :=
  let declName := Name.replacePrefix pref new_pref ctor.declName
  {
    declName,
    ref := ctor.ref
    modifiers := ctor.modifiers
    binders := ctor.binders
    type? := ctor.type?
  }



open Parser in
/--
  Defines the "head" type of a polynomial functor

  That is, it defines a type with exactly as many constructor as the input type, but such that
  all constructors are constants (take no arguments).
-/
def mkHeadT (view : InductiveView) : CommandElabM Name := do
  -- If the original declId was `MyType`, we want to register the head type under `MyType.HeadT`
  let suffix := "HeadT"
  let declName := Name.mkStr view.declName suffix
  let declId := mkNode ``Command.declId #[mkIdent declName, mkNullNode]
  let shortDeclName := Name.mkSimple suffix

  let modifiers : Modifiers := {
    isUnsafe := view.modifiers.isUnsafe
  }
  -- The head type is the same as the original type, but with all constructor arguments removed
  let ctors ← view.ctors.mapM fun ctor => do
    let declName := Name.replacePrefix view.declName declName ctor.declName
    pure { 
      modifiers, declName,
      ref := ctor.ref
      binders := mkNullNode
      type? := none
      : CtorView
    } 

  -- let type ← `(Type $(mkIdent `u))

  -- TODO: make `HeadT` universe polymorphic
  let view := {
    ctors, declId, declName, shortDeclName, modifiers,
    binders         := view.binders.setArgs #[]
    levelNames      := view.levelNames

    ref             := view.ref            
    type?           := view.type?
    
    derivingClasses := view.derivingClasses
    : InductiveView
  }

  -- dbg_trace "mkHeadT :: elabInductiveViews"
  elabInductiveViews #[view]
  pure declName


open Parser in
private def matchAltsOfArray (matchAlts : Array Syntax) : Syntax :=
  mkNode ``Term.matchAlts #[mkNullNode matchAlts]


open Parser in
/--
  Wraps an array of `matchAltExpr` syntax objects into a single `Command.declValEqns` node, for
  use in inductive definitions
-/
private def declValEqnsOfMatchAltArray (matchAlts : Array Syntax) : Syntax :=
  let body := matchAltsOfArray matchAlts
  let body := mkNode ``Term.matchAltsWhereDecls #[body, mkNullNode]
  mkNode ``Command.declValEqns #[body]


open Parser Parser.Term Parser.Command in
/--
  Defines the "child" family of type vectors for an `n`-ary polynomial functor

  That is, it defines a type `ChildT : HeadT → TypeVec n` such that number of inhabitants of
  `ChildT a i` corresponds to the times that constructor `a` takes an argument of the `i`-th type
  argument
-/
def mkChildT (view : InductiveView) (r : Replace) (headTName : Name) : CommandElabM Name := do  
  -- If the original declId was `MyType`, we want to register the child type under `MyType.ChildT`
  let suffix := "ChildT"
  let declName := Name.mkStr view.declName suffix
  let declId := mkNode ``Command.declId #[mkIdent declName, mkNullNode]
  let shortDeclName := Name.mkSimple suffix

  let target_type := Syntax.mkApp (mkIdent ``TypeVec) #[quote r.arity]

  let binderIdents := r.getBinderIdents
  let matchAlts ← view.ctors.mapM fun ctor => do  
    let head := mkIdent $ Name.replacePrefix view.declName headTName ctor.declName 

    let counts := countVarOccurences r ctor.type?
    let counts := counts.map fun n => 
                    Syntax.mkApp (mkIdent ``PFin2) #[quote n]
    let counts := counts.reverse

    `(matchAltExpr| | $head => (![ $counts,* ]))

  let body := declValEqnsOfMatchAltArray matchAlts
  let headT := mkIdent headTName

  

  let cmd ← `(
    def $declId : $headT → $target_type
      $body:declValEqns
  )

  -- dbg_trace "mkChildT :: elabCommand"
  elabCommand cmd

  pure declName

open Parser.Term in
/--
  Show that the `Shape` type is a qpf, through an isomorphism with the `Shape.P` pfunctor
-/
def mkQpf (shapeView : InductiveView) (ctorArgs : Array CtorArgs) (headT childT P : Syntax) (arity : Nat) : CommandElabM Unit := do
  let shapeN := shapeView.declName
  let q := mkIdent $ Name.mkStr shapeN "qpf"
  let shape := mkIdent shapeN

  let n_ctors := shapeView.ctors.size;
  let ctors := shapeView.ctors.zip ctorArgs

  /-
    `box` maps objects from the curried form, to the internal uncurried form.
    See below, or [.ofPolynomial] for the signature

    Example, using a simple list type
    ```lean4
     fun x => match x with
    | MyList.Shape.nil a b => ⟨MyList.Shape.HeadT.nil, fun i => match i with
        | 0 => Fin2.elim0 (C:=fun _ => _)
        | 1 => fun j => match j with 
                | (.ofNat' 0) => b
        | 2 => fun j => match j with 
                | (.ofNat' 0) => a
    ⟩
    | MyList.Shape.cons a as => ⟨MyList.Shape.HeadT.cons, fun i j => match i with
        | 0 => match j with
                | .fz => as
        | 1 => Fin2.elim0 (C:=fun _ => _) j
        | 2 => match j with
                | .fz => a
    ```
  -/

  let boxBody ← ctors.mapM fun (ctor, args) => do
    let argsId  := args.args.map mkIdent
    let alt     := mkIdent ctor.declName
    let headAlt := mkIdent $ Name.replacePrefix shapeView.declName headT.getId ctor.declName

    `(matchAltExpr| | $alt:ident $argsId:ident* => ⟨$headAlt:ident, fun i => match i with
        $(
          ←args.per_type.enum.mapM fun (i, args) => do
            let i := arity - 1 - i
            let body ← if args.size == 0 then
                          -- `(fun j => Fin2.elim0 (C:=fun _ => _) j)
                          `(PFin2.elim0)
                        else
                          let alts ← args.enum.mapM fun (j, arg) =>
                              let arg := mkIdent arg
                              `(matchAltExpr| | $(PFin2.quoteOfNat j) => $arg)
                          `(
                            fun j => match j with
                              $alts:matchAlt*
                          )
            `(matchAltExpr| | $(PFin2.quoteOfNat i) => $body)
        ):matchAlt*
    ⟩)
  let box ← `(
    fun x => match x with
      $boxBody:matchAlt*
  )

  /-
    `unbox` does the opposite of `box`; it maps from uncurried to curried

    fun ⟨head, child⟩ => match head with
    | MyList.Shape.HeadT.nil  => MyList.Shape.nil (child 2 .fz) (child 1 .fz)
    | MyList.Shape.HeadT.cons => MyList.Shape.cons (child 2 .fz) (child 0 .fz)
  -/

  /- the `child` variable in the example above -/
  let unbox_child := mkIdent <|<- Elab.Term.mkFreshBinderName;
  let unboxBody ← ctors.mapM fun (ctor, args) => do
    let alt     := mkIdent ctor.declName
    let headAlt := mkIdent $ Name.replacePrefix shapeView.declName headT.getId ctor.declName
      
    let args : Array Syntax ← args.args.mapM fun arg => do
      -- find the pair `(i, j)` such that the argument is the `j`-th occurence of the `i`-th type
      let (i, j) := (args.per_type.enum.map fun (i, t) => 
        -- the order of types is reversed, since `TypeVec`s count right-to-left
        let i := arity - 1 - i 
        ((t.indexOf? arg).map fun ⟨j, _⟩ => (i, j)).toList
      ).toList.join.get! 0

      `($unbox_child $(PFin2.quoteOfNat i) $(PFin2.quoteOfNat j))

    let body := Syntax.mkApp alt args

    `(matchAltExpr| | $headAlt:ident => $body)

  let unbox ← `(
    fun ⟨head, $unbox_child⟩ => match head with
        $unboxBody:matchAlt*
  )

  let cmd ← `(
    instance $q:ident : MvQpf (@TypeFun.ofCurried $(quote arity) $shape) :=
      MvQpf.ofPolynomial $P $box $unbox (
        by 
          intro _ x;
          rcases x with ⟨head, child⟩;
          cases head
          <;> simp
          <;> apply congrArg
          <;> fin_destr
          <;> rfl          
      ) (
        by 
          intro _ x;
          cases x
          <;> rfl
      )
  )
  -- dbg_trace f!"\nqpf: {cmd}\n"
  elabCommand cmd

  pure ()









structure MkShapeResult where
  (r : Replace)
  (shape : Name)
  (P : Name)

open Parser in
def mkShape (view: InductiveView) : CommandElabM MkShapeResult := do
  -- If the original declId was `MyType`, we want to register the shape type under `MyType.Shape`
  let suffix := "Shape"
  let declName := Name.mkStr view.declName suffix
  let declId := mkNode ``Command.declId #[mkIdent declName, mkNullNode]
  let shortDeclName := Name.mkSimple suffix


  -- Extract the "shape" functors constructors
  let shapeIdent  := mkIdent shortDeclName
  let ((ctors, ctorArgs), r) ← Replace.run (Replace.shapeOfCtors view shapeIdent)
  let ctors := ctors.map (CtorView.declReplacePrefix view.declName declName)

  -- Assemble it back together, into the shape inductive type
  let binders ← r.getBinders  
  let binders := view.binders.setArgs #[binders]
  let modifiers : Modifiers := {
    isUnsafe := view.modifiers.isUnsafe
  }
  let view := {
    ctors, declId, declName, shortDeclName, modifiers, binders,
    levelNames      := []

    ref             := view.ref            
    type?           := view.type?          
    
    derivingClasses := view.derivingClasses
    : InductiveView
  }

  -- dbg_trace "mkShape :: elabInductiveViews"
  elabInductiveViews #[view]

  let headTName ← mkHeadT view
  let childTName ← mkChildT view r headTName

  let PName := Name.mkStr declName "P"
  let PId := mkIdent PName
  -- let u ← Elab.Term.mkFreshBinderName
  let PDeclId := mkNode ``Command.declId #[PId, mkNullNode 
    -- #[ TODO: make this universe polymorphic
    --   mkAtom ".{",
    --   mkNullNode #[u],
    --   mkAtom "}"
    -- ]
  ]

  let headTId := mkIdent headTName
  let childTId := mkIdent childTName

  elabCommand <|<- `(
    def $PDeclId := 
      MvPFunctor.mk $headTId $childTId
  )

 
  mkQpf view ctorArgs headTId childTId PId r.arity
  

  pure ⟨r, declName, PName⟩  







/--
  Return a syntax tree for `MvQpf.Fix` or `MvQpf.Cofix` when self is `Data`, resp. `Codata`.
-/
def DataCommand.fixOrCofix : DataCommand → Syntax
  := fun cmd => mkIdent $ match cmd with
      | .Data   => ``_root_.MvQpf.Fix
      | .Codata => ``_root_.MvQpf.Cofix

open Macro Comp in
/--
  Top-level elaboration for both `data` and `codata` declarations
-/
@[commandElab declaration]
def elabData : CommandElab := fun stx => do 
  let modifiers ← elabModifiers stx[0]
  let decl := stx[1]
  let view ← dataSyntaxToView modifiers decl
  

  let (view, rho) ← makeNonRecursive view;

  let ⟨r, shape, P⟩ ← mkShape view.asInductive

      
  let base ← elabQpfCompositionBody {
    liveBinders := view.liveBinders, 
    deadBinders := view.deadBinders,     
    type?   := none,
    target  := ←`(
      $(mkIdent shape):ident $r.expr*
    )
  }


  let uncurried := mkIdent $ Name.mkStr view.declName "Uncurried"

  let (deadBindersNoHoles, deadBinderNames) ← mkFreshNamesForBinderHoles view.deadBinders
  let deadBinderNamedArgs ← deadBinderNames.mapM fun n => `(Parser.Term.namedArgument| ($n:ident := $n:term))
  let uncurried_applied := Syntax.mkApp uncurried deadBinderNamedArgs

  /- At this point, `view` still contains the extra recursive parameter, so the final arity is 1 less -/
  let arity := quote (view.liveBinders.size - 1)
  let fix_or_cofix := DataCommand.fixOrCofix view.command
  let cmd ← `(
    abbrev $uncurried:ident $deadBindersNoHoles:bracketedBinder* : _root_.TypeFun $arity
      := $fix_or_cofix $base

    abbrev $(view.declId)   $deadBindersNoHoles:bracketedBinder*
      := _root_.TypeFun.curried $uncurried_applied
  ) 
  -- dbg_trace "{cmd}"
  elabCommand cmd

end Data.Command


