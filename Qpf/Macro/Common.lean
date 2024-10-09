import Qpf.Qpf

namespace Macro
  open Lean Meta Elab Term
  open Elab.Command (CommandElabM)

  open Lean.Parser.Term (binderIdent bracketedBinder)

  initialize
    registerTraceClass `QPF


  variable [MonadControlT MetaM n] [Monad n] [MonadLiftT MetaM n]
            [MonadError n] [MonadLog n] [AddMessageContext n]
            [MonadQuotation n] [MonadTrace n] [MonadOptions n]
            [MonadLiftT IO n] [MonadAlwaysExcept ε n] [MonadLiftT BaseIO n]

/-- Add trace node with the `QPF` trace class -/
def withQPFTraceNode (header : MessageData) (k : n α)
    (collapsed : Bool := true) (tag : String := "")
    : n α := do
  Lean.withTraceNode `QPF (fun _ => pure header) k collapsed tag

/-- Wrapper around `elabCommand` which first traces the command syntax
(in a `QPF` trace node), before elaborating the command -/
def elabCommandAndTrace (stx : Syntax)
    (header : MessageData := "elaborating command …") :
    CommandElabM Unit := do
  withQPFTraceNode header <| do
    trace[QPF] stx
  Lean.Elab.Command.elabCommand stx

  /--
    Takes an expression `e` of type `CurriedTypeFun n` and returns an expression of type `TypeFun n`
    representing the uncurried version of `e`.
    Tries to prevent unneccesary `ofCurried / curried` roundtrips
  -/
  def uncurry (F : Expr) (arity : Option Expr := none) : n Expr := do
    mkAppOptM ``TypeFun.ofCurried #[arity, some F]

    --
    -- Although preventing unneccesary `ofCurried / curried` roundtrips seems like a good idea,
    -- leaving them in actually causes more definitional equality (e.g., in the `_02_Tree` example)
    --

    -- let n       ← mkFreshExprMVar (mkConst ``Nat)
    -- let F_inner ← mkFreshExprMVar (kind:=MetavarKind.synthetic) none
    -- let us      ← mkFreshLevelMVars 2
    -- let app     := mkApp2 (mkConst ``TypeFun.curried us) n F_inner

    -- trace[QPF] "\nChecking defEq of {F} and {app}"
    -- if (←isDefEq F app) then
    --   if let some F' :=  (← getExprMVarAssignment? F_inner.mvarId!) then
    --     trace[QPF] "yes: {F'}"
    --     return F'

    -- trace[QPF] "no"
    -- mkAppM ``TypeFun.ofCurried #[F]



  def withLiveBinders [Inhabited α]
                  (binders : Array Syntax)
                  (f : Array Expr → n α) : n α
  := do
    let u := mkLevelSucc <|← mkFreshLevelMVar;
    let decls := binders.map fun α => (
      let α := if α.getKind == ``Parser.Term.binderIdent then
        α[0]
      else
        α
      α.getId,
      fun _ => pure (mkSort u)
    )

    withLocalDeclsD decls f



  /--
    Takes an array of bracketed binders, and allocate a fresh identifier for each hole in the binders.
    Returns a pair of the binder syntax with all holes replaced, and an array of all bound identifiers,
    both pre-existing and newly created
  -/
  def mkFreshNamesForBinderHoles (binders : Array Syntax) :
      n ((TSyntaxArray ``bracketedBinder) × (Array Ident)) :=
    withQPFTraceNode "mkFreshNamesForBinderHoles"
      (tag := "mkFreshNamesForBinderHoles") (collapsed := false) do

    let mut bindersNoHoles := #[]
    let mut binderNames := #[]

    for stx in binders do
      let mut newArgStx := Syntax.missing
      let kind := stx.getKind

      if kind == ``Lean.Parser.Term.instBinder then
        if stx[1].isNone then
          throwErrorAt stx "Instances without names are not supported yet"
          -- let id := mkIdentFrom stx (← mkFreshBinderName)
          -- binderNames := binderNames.push id
          -- newArgStx := stx[1].setArgs #[id, Syntax.atom SourceInfo.none ":"]
        else
          trace[QPF] stx[1]
          let id := stx[1][0]
          binderNames := binderNames.push ⟨id⟩
          newArgStx := stx[1]

      else
        -- replace each hole with a fresh id
        let ids ← stx[1].getArgs.mapM fun (id : Syntax) => do
          trace[QPF] "{id}"
          let kind := id.getKind
          if kind == identKind then
            return id
          else if kind == ``Lean.Parser.Term.hole then
            return mkIdentFrom id (← mkFreshBinderName)
          else
            throwErrorAt id "identifier or `_` expected, found {kind}"

        for id in ids do
          binderNames := binderNames.push ⟨id⟩
        newArgStx := stx[1].setArgs ids

      let newStx := stx.setArg 1 newArgStx
      bindersNoHoles := bindersNoHoles.push ⟨newStx⟩

    return (bindersNoHoles, binderNames)


  inductive BinderKind
    | explicit
    | implicit
    | ident
    deriving DecidableEq, BEq, Inhabited


  open Lean.Parser.Term (explicitBinder implicitBinder) in
  /-- Parse a `BinderKind` from a `SyntaxNodeKind` -/
  def BinderKind.ofSyntaxKind (kind : SyntaxNodeKind) : BinderKind :=
    if kind == ``implicitBinder then
          .implicit
        else if kind == ``Lean.binderIdent
                || kind == ``Lean.Parser.Term.binderIdent
                || kind == ``Lean.Parser.Term.ident
                || kind == ``Lean.Parser.ident
                -- HACK: this one should be just a single backquote
                || kind == `ident
                then
          .ident
        else if kind == ``explicitBinder then
          .explicit
        else
          panic s!"Bug: unexpected binder kind `{kind}"


  open Lean.Parser.Term in
  /--
    Takes a list of binders, and split it into live and dead binders, respectively.
    For the live binders, return an array of with syntax of kind `binderIdent`, unwrapping
    `simpleBinder` nodes if needed (while asserting that there were no type annotations)
  -/
  def splitLiveAndDeadBinders (binders : Array Syntax)
      : n (TSyntaxArray ``Lean.Parser.Term.binderIdent × TSyntaxArray ``bracketedBinder) := do
    let mut liveVars := #[]
    let mut deadBinders := #[]

    let mut isLive := false
    for binder in binders do
      let kind := BinderKind.ofSyntaxKind binder.getKind

      if kind == .ident then
        isLive := true
        liveVars := liveVars.push ⟨binder⟩

      -- else if kind == .explicit then
      --   isLive := true
      --   for id in binder[0].getArgs do
      --     liveVars := liveVars.push id

      --   if !binder[1].isNone then
      --     trace[QPF] binder[1]
      --     throwErrorAt binder "live variable may not have a type annotation.\nEither add brackets to mark the variable as dead, or remove the type"

      else if isLive then
        throwErrorAt binder f!"Unexpected bracketed binder, dead arguments must precede all live arguments.\nPlease reorder your arguments or mark this binder as live by removing brackets and/or type ascriptions"

      else
        deadBinders := deadBinders.push ⟨binder⟩

    return (liveVars, deadBinders)






  /--
    Takes a list of binders, and returns an array of just the bound identifiers,
    for use in applications
  -/
  def getBinderIdents (binders : Array Syntax) (includeImplicits := true)
    : Array Term :=
  Id.run do
    let mut idents : Array Term := #[]

    for binder in binders do
      let kind := BinderKind.ofSyntaxKind binder.getKind

      if kind == .implicit && !includeImplicits then
        continue

      else if kind == .ident then
        idents := idents.push ⟨binder⟩

      else
        for id in binder[1].getArgs do
          idents := idents.push ⟨id⟩


    -- dbg_trace "idents = {idents}"
    pure idents




open Parser.Command in
instance : Quote Modifiers (k := ``declModifiers) where
  quote mod :=
    let isNoncomputable : Syntax :=
      if mod.isNoncomputable then
        mkNode ``«noncomputable» #[mkAtom "noncomputable "]
      else
        mkNullNode

    let visibility := match mod.visibility with
      | .regular     => mkNullNode
      | .«protected» => mkNode ``«protected» #[mkAtom "protected "]
      | .«private»   => mkNode ``«private» #[mkAtom "private "]

    mkNode ``declModifiers #[
      mkNullNode, -- docComment
      mkNullNode, -- Term.attributes
      visibility, -- visibility
      isNoncomputable, -- isNoncomputable
      mkNullNode, -- unsafe
      mkNullNode  -- partial / nonrec
    ]


  -- open Lean.Parser.Term in
  -- elab "#dbg_syntax " t:term : command => do
  --   dbg_trace t


  -- open Lean.Parser.Term Elab.Command in
  -- elab "#dbg_expr " t:term : command => do
  --   let expr ← liftTermElabM none $ elabTerm t none
  --   dbg_trace expr
  --   dbg_trace expr.isForall

  -- #dbg_expr (Nat → Int)

end Macro


-- set_option pp.raw true

-- open Lean in
-- elab "#dbg_ident" id:binderIdent : command => do
--   dbg_trace "{id}"
--   let id := id.raw
--   dbg_trace "kind: {id.getKind}"
--   dbg_trace "args: {id.getArgs}"
--   dbg_trace "args[0].getKind: {id.getArgs[0]!.getKind}"

-- #dbg_ident x
-- #dbg_ident _

-- example : ``Lean.binderIdent = ``Lean.Parser.Term.binderIdent :=
--   by rfl
