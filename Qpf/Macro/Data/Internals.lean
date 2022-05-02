
import Lean
import Qpf.Macro.Data.DataDecl

/-!
  The `data` command is intended as a drop-in replacement for `inductive`, so it makes sense to 
  reuse as much of the elaborator for `inductive`.
  Since most of the relevant functions are marked private, we duplicate the code here.

  Code is taken from lean version nightly-2022-03-17. 
  TODO: licensing?
-/

open Lean
open Meta Elab Elab.Command 

namespace Internals

/-
  Taken from Lean.Elab.Declaration
-/
section
/-

leading_parser "inductive " >> declId >> optDeclSig >> optional ":=" >> many ctor
leading_parser atomic (group ("class " >> "inductive ")) >> declId >> optDeclSig >> optional ":=" >> many ctor >> optDeriving
-/
def inductiveSyntaxToView (modifiers : Modifiers) (decl : Syntax) : CommandElabM InductiveView := do
  checkValidInductiveModifier modifiers
  let (binders, type?) := expandOptDeclSig decl[2]
  let declId           := decl[1]
  let ⟨name, declName, levelNames⟩ ← expandDeclId declId modifiers
  addDeclarationRanges declName decl
  let ctors      ← decl[4].getArgs.mapM fun ctor => withRef ctor do
    -- def ctor := leading_parser " | " >> declModifiers >> ident >> optional inferMod >> optDeclSig
    let ctorModifiers ← elabModifiers ctor[1]
    if ctorModifiers.isPrivate && modifiers.isPrivate then
      throwError "invalid 'private' constructor in a 'private' inductive datatype"
    if ctorModifiers.isProtected && modifiers.isPrivate then
      throwError "invalid 'protected' constructor in a 'private' inductive datatype"
    checkValidCtorModifier ctorModifiers
    let ctorName := ctor.getIdAt 2
    let ctorName := declName ++ ctorName
    let ctorName ← withRef ctor[2] $ applyVisibility ctorModifiers.visibility ctorName
    let inferMod := !ctor[3].isNone
    let (binders, type?) := expandOptDeclSig ctor[4]
    addDocString' ctorName ctorModifiers.docString?
    addAuxDeclarationRanges ctorName ctor ctor[2]
    pure { ref := ctor, modifiers := ctorModifiers, declName := ctorName, inferMod := inferMod, binders := binders, type? := type? : CtorView }
  let classes ← getOptDerivingClasses decl[5]
  pure {
    ref             := decl
    modifiers       := modifiers
    shortDeclName   := name
    declName        := declName
    levelNames      := levelNames
    binders         := binders
    type?           := type?
    ctors           := ctors
    derivingClasses := classes
  }

end

/-
  Taken from Lean.Elab.Inductive
-/
section

private partial def elabHeaderAux (views : Array InductiveView) (i : Nat) (acc : Array ElabHeaderResult) : TermElabM (Array ElabHeaderResult) := do
  if h : i < views.size then
    let view := views.get ⟨i, h⟩
    let acc ← Term.withAutoBoundImplicit <| Term.elabBinders view.binders.getArgs fun params => do
      match view.type? with
      | none         =>
        let u ← mkFreshLevelMVar
        let type := mkSort u
        Term.synthesizeSyntheticMVarsNoPostponing
        Term.addAutoBoundImplicits params fun params => do
          pure <| acc.push { lctx := (← getLCtx), localInsts := (← getLocalInstances), params, type, view }
      | some typeStx =>
        let (type, numImplicitIndices) ← Term.withAutoBoundImplicit do
          let type ← Term.elabType typeStx
          unless (← isTypeFormerType type) do
            throwErrorAt typeStx "invalid inductive type, resultant type is not a sort"
          Term.synthesizeSyntheticMVarsNoPostponing
          Term.addAutoBoundImplicits #[] fun indices =>
            return (← mkForallFVars indices type, indices.size)
        Term.addAutoBoundImplicits params fun params => do
          pure <| acc.push { lctx := (← getLCtx), localInsts := (← getLocalInstances), params, type, view }
    elabHeaderAux views (i+1) acc
  else
    pure acc

private def mkTypeFor (r : ElabHeaderResult) : TermElabM Expr := do
  withLCtx r.lctx r.localInsts do
    mkForallFVars r.params r.type


private def elabHeader (views : Array InductiveView) : TermElabM (Array ElabHeaderResult) := do
  let rs ← elabHeaderAux views 0 #[]
  /- We don't support `mutual` declarations, so no need for these checks
  if rs.size > 1 then
    checkUnsafe rs
    let numParams ← checkNumParams rs
    checkHeaders rs numParams 0 none
  -/
  return rs



/- Create a local declaration for each inductive type in `rs`, and execute `x params indFVars`, where `params` are the inductive type parameters and
   `indFVars` are the new local declarations.
   We use the local context/instances and parameters of rs[0].
   Note that this method is executed after we executed `checkHeaders` and established all
   parameters are compatible. -/
private partial def withInductiveLocalDecls {α} (rs : Array ElabHeaderResult) (x : Array Expr → Array Expr → TermElabM α) : TermElabM α := do
  let namesAndTypes ← rs.mapM fun r => do
    let type ← mkTypeFor r
    pure (r.view.shortDeclName, type)
  let r0     := rs[0]
  let params := r0.params
  withLCtx r0.lctx r0.localInsts $ withRef r0.view.ref do
    let rec loop (i : Nat) (indFVars : Array Expr) := do
      if h : i < namesAndTypes.size then
        let (id, type) := namesAndTypes.get ⟨i, h⟩
        withLocalDeclD id type fun indFVar => loop (i+1) (indFVars.push indFVar)
      else
        x params indFVars
    loop 0 #[]

private def isInductiveFamily (numParams : Nat) (indFVar : Expr) : TermElabM Bool := do
  let indFVarType ← inferType indFVar
  forallTelescopeReducing indFVarType fun xs _ =>
    return xs.size > numParams



/-- Return free variables of `e` -/
def Expr.getFVar (e : Expr) : List Expr :=
  if !e.hasFVar then [] else
    match e with
    | Expr.forallE _ d b _   => getFVar d ++ getFVar b
    | Expr.lam _ d b _       => getFVar d ++ getFVar b
    | Expr.mdata _ e _       => getFVar e
    | Expr.letE _ t v b _    => getFVar t ++ getFVar v ++ getFVar b
    | Expr.app f a _         => getFVar f ++ getFVar a
    | Expr.proj _ _ e _      => getFVar e
    | e@(Expr.fvar fvarId _) => [e] --[fvarId]
    | e                      => []

/--
  New function
  Return all "dead" parameters, i.e., parameters that occur on the left-hand side of an arrow

  We keep free variables as `Expr`, rather than the more constrained `FVarId`s, since the former
  pretty-prints with user-defined names (i.e., so that we get `β` rather than some internal `uniq_123`)
-/
private def getDeadParams  : (argType : Expr) → List Expr
  | Expr.forallE _ lhs rhs .. => Expr.getFVar lhs ++ getDeadParams rhs
  | Expr.lam _ d b _          => getDeadParams d ++ getDeadParams b
  | Expr.mdata _ e _          => getDeadParams e
  | Expr.letE _ t v b _       => getDeadParams t ++ getDeadParams v ++ getDeadParams b
  | Expr.app f a _            => getDeadParams f ++ getDeadParams a
  | Expr.proj _ _ e _         => getDeadParams e
  | e                         => []

/--
  New function
  Reduce an arrow type `a → b → ... → c` to a list of arguments `[a, b, ...]`, and then 
  return the dead parameters of those arguments
-/
private partial def getDeadParamsOfArgs (ctorType : Expr) : TermElabM (List Expr) :=
  forallTelescopeReducing ctorType fun args _ => do
    let argTypes ← liftMetaM $ args.mapM inferType 
    pure $ List.join $ argTypes.toList.map getDeadParams

/-
  Returns elaborated constructor types and a list of dead parameters.

  Remark: we check whether the resulting type is correct, and the parameter occurrences are consistent, but
  we currently do not check for:
  - Universe constraints (the kernel checks for it).

  This modified version does check for positivity, and it will return a list of variables that occur 
  "negatively" (also called being "dead")
-/
private def elabCtors (indFVars : Array Expr) (indFVar : Expr) (params : Array Expr) (r : ElabHeaderResult) 
      : TermElabM (List Constructor × List Expr) := 
withRef r.view.ref do
  let indFamily ← isInductiveFamily params.size indFVar
  let ctors ← r.view.ctors.toList.mapM fun ctorView => do
    Term.withAutoBoundImplicit <| Term.elabBinders ctorView.binders.getArgs fun ctorParams => do
      -- use `withNestedTraces` to allow traces to bubble up
      withNestedTraces $ withRef ctorView.ref do        
        let rec elabCtorType (k : Expr → TermElabM (Constructor × List Expr)) : TermElabM (Constructor × List Expr) := do
          match ctorView.type? with
          | none          =>
            if indFamily then
              throwError "constructor resulting type must be specified in inductive family declaration"
            k <| mkAppN indFVar params
          | some ctorType =>
            let type ← Term.elabType ctorType
            Term.synthesizeSyntheticMVars (mayPostpone := true)
            let type ← instantiateMVars type
            let type ← checkParamOccs type
            forallTelescopeReducing type fun _ resultingType => do
              unless resultingType.getAppFn == indFVar do
                throwError "unexpected constructor resulting type{indentExpr resultingType}"
              unless (← isType resultingType) do
                throwError "unexpected constructor resulting type, type expected{indentExpr resultingType}"
            k type
        elabCtorType fun type => do
          -- Dead parameter check
          let deadParams ← getDeadParamsOfArgs type
          if deadParams.contains indFVar then
            throwError "'{ctorView.declName}' has a non positive occurrence of the datatypes being declared"
          Term.synthesizeSyntheticMVarsNoPostponing
          Term.addAutoBoundImplicits ctorParams fun ctorParams => do
            let type ← mkForallFVars ctorParams type
            Term.mvarsToParams type fun extraCtorParams type => do
              let type ← mkForallFVars extraCtorParams type
              let type ← mkForallFVars params type
              let ctor := { name := ctorView.declName, type }
              return ⟨ctor, deadParams⟩
  let deadParams := List.join $ ctors.map (·.2)
  let ctors := ctors.map (·.1)
  pure ⟨ctors, deadParams⟩
where
  checkParamOccs (ctorType : Expr) : MetaM Expr :=
    let visit (e : Expr) : MetaM TransformStep := do
      let f := e.getAppFn
      if indFVars.contains f then
        let mut args := e.getAppArgs
        unless args.size ≥ params.size do
          throwError "unexpected inductive type occurrence{indentExpr e}"
        for i in [:params.size] do
          let param := params[i]
          let arg := args[i]
          unless (← isDefEq param arg) do
            throwError "inductive datatype parameter mismatch{indentExpr arg}\nexpected{indentExpr param}"
          args := args.set! i param
        return TransformStep.done (mkAppN f args)
      else
        return TransformStep.visit e
    transform ctorType (pre := visit)



/- Convert universe metavariables occurring in the `indTypes` into new parameters.
   Remark: if the resulting inductive datatype has universe metavariables, we will fix it later using
   `inferResultingUniverse`. -/
private def levelMVarToParamAux (indTypes : List InductiveType) : StateRefT Nat TermElabM (List InductiveType) :=
  indTypes.mapM fun indType => do
    let type  ← Term.levelMVarToParam' indType.type
    let ctors ← indType.ctors.mapM fun ctor => do
      let ctorType ← Term.levelMVarToParam' ctor.type
      pure { ctor with type := ctorType }
    pure { indType with ctors := ctors, type := type }

private def levelMVarToParam (indTypes : List InductiveType) : TermElabM (List InductiveType) :=
  (levelMVarToParamAux indTypes).run' 1

private def getResultingUniverse : List InductiveType → TermElabM Level
  | []           => throwError "unexpected empty inductive declaration"
  | indType :: _ => forallTelescopeReducing indType.type fun _ r => do
    let r ← whnfD r
    match r with
    | Expr.sort u _ => pure u
    | _             => throwError "unexpected inductive type resulting type{indentExpr r}"

/- Auxiliary function for `updateResultingUniverse` -/
private partial def collectUniversesFromCtorTypeAux (r : Level) (rOffset : Nat) : Nat → Expr → Array Level → TermElabM (Array Level)
  | 0,   Expr.forallE n d b c, us => do
    let u ← getLevel d
    let u ← instantiateLevelMVars u
    let us ← accLevelAtCtor u r rOffset us
    withLocalDecl n c.binderInfo d fun x =>
      let e := b.instantiate1 x
      collectUniversesFromCtorTypeAux r rOffset 0 e us
  | i+1, Expr.forallE n d b c, us => do
    withLocalDecl n c.binderInfo d fun x =>
      let e := b.instantiate1 x
      collectUniversesFromCtorTypeAux r rOffset i e us
  | _, _, us => pure us

/- Auxiliary function for `updateResultingUniverse` -/
private partial def collectUniversesFromCtorType
    (r : Level) (rOffset : Nat) (ctorType : Expr) (numParams : Nat) (us : Array Level) : TermElabM (Array Level) :=
  collectUniversesFromCtorTypeAux r rOffset numParams ctorType us

/- Auxiliary function for `updateResultingUniverse` -/
private partial def collectUniverses (r : Level) (rOffset : Nat) (numParams : Nat) (indTypes : List InductiveType) : TermElabM (Array Level) := do
  let mut us := #[]
  for indType in indTypes do
    for ctor in indType.ctors do
      us ← collectUniversesFromCtorType r rOffset ctor.type numParams us
  return us

private def updateResultingUniverse (numParams : Nat) (indTypes : List InductiveType) : TermElabM (List InductiveType) := do
  let r ← getResultingUniverse indTypes
  let rOffset : Nat   := r.getOffset
  let r       : Level := r.getLevelOffset
  unless r.isParam do
    throwError "failed to compute resulting universe level of inductive datatype, provide universe explicitly"
  let us ← collectUniverses r rOffset numParams indTypes
  trace[Elab.inductive] "updateResultingUniverse us: {us}, r: {r}, rOffset: {rOffset}"
  let rNew := mkResultUniverse us rOffset
  let updateLevel (e : Expr) : Expr := e.replaceLevel fun u => if u == tmpIndParam then some rNew else none
  return indTypes.map fun indType =>
    let type := updateLevel indType.type;
    let ctors := indType.ctors.map fun ctor => { ctor with type := updateLevel ctor.type };
    { indType with type := type, ctors := ctors }

register_builtin_option bootstrap.inductiveCheckResultingUniverse : Bool := {
    defValue := true,
    group    := "bootstrap",
    descr    := "by default the `inductive/structure commands report an error if the resulting universe is not zero, but may be zero for some universe parameters. Reason: unless this type is a subsingleton, it is hardly what the user wants since it can only eliminate into `Prop`. In the `Init` package, we define subsingletons, and we use this option to disable the check. This option may be deleted in the future after we improve the validator"
}
private def checkResultingUniverses (indTypes : List InductiveType) : TermElabM Unit := do
  checkResultingUniverse (← getResultingUniverse indTypes)

private def collectUsed (indTypes : List InductiveType) : StateRefT CollectFVars.State MetaM Unit := do
  indTypes.forM fun indType => do
    Meta.collectUsedFVars indType.type
    indType.ctors.forM fun ctor =>
      Meta.collectUsedFVars ctor.type

private def removeUnused (vars : Array Expr) (indTypes : List InductiveType) : TermElabM (LocalContext × LocalInstances × Array Expr) := do
  let (_, used) ← (collectUsed indTypes).run {}
  Meta.removeUnused vars used

private def withUsed {α} (vars : Array Expr) (indTypes : List InductiveType) (k : Array Expr → TermElabM α) : TermElabM α := do
  let (lctx, localInsts, vars) ← removeUnused vars indTypes
  withLCtx lctx localInsts $ k vars

private def getArity (indType : InductiveType) : MetaM Nat :=
  forallTelescopeReducing indType.type fun xs _ => return xs.size

/--
  Compute a bit-mask that for `indType`. The size of the resulting array `result` is the arity of `indType`.
  The first `numParams` elements are `false` since they are parameters.
  For `i ∈ [numParams, arity)`, we have that `result[i]` if this index of the inductive family is fixed.
-/
private def computeFixedIndexBitMask (numParams : Nat) (indType : InductiveType) (indFVars : Array Expr) : MetaM (Array Bool) := do
  let arity ← getArity indType
  if arity ≤ numParams then
    return mkArray arity false
  else
    let maskRef ← IO.mkRef (mkArray numParams false ++ mkArray (arity - numParams) true)
    let rec go (ctors : List Constructor) : MetaM (Array Bool) := do
      match ctors with
      | [] => maskRef.get
      | ctor :: ctors =>
        forallTelescopeReducing ctor.type fun xs type => do
          let I := type.getAppFn.constName!
          let typeArgs := type.getAppArgs
          for i in [numParams:arity] do
            unless i < xs.size && xs[i] == typeArgs[i] do -- Remark: if we want to allow arguments to be rearranged, this test should be xs.contains typeArgs[i]
              maskRef.modify fun mask => mask.set! i false
          for x in xs[numParams:] do
            let xType ← inferType x
            xType.forEach fun e => do
              if indFVars.any (fun indFVar => e.getAppFn == indFVar) && e.getAppNumArgs > numParams then
                let eArgs := e.getAppArgs
                for i in [numParams:eArgs.size] do
                  if i >= typeArgs.size then
                    maskRef.modify fun mask => mask.set! i false
                  else
                    unless eArgs[i] == typeArgs[i] do
                      maskRef.modify fun mask => mask.set! i false
        go ctors
    go indType.ctors

/-- Return true iff `arrowType` is an arrow and its domain is defeq to `type` -/
private def isDomainDefEq (arrowType : Expr) (type : Expr) : MetaM Bool := do
  if !arrowType.isForall then
    return false
  else
    withNewMCtxDepth do -- Make sure we do not assign univers metavariables
      isDefEq arrowType.bindingDomain! type


/--
  Convert fixed indices to parameters.
  TODO: we currently only convert a prefix of the indices, and we do not try to reorder binders.
-/
private partial def fixedIndicesToParams (numParams : Nat) (indTypes : Array InductiveType) (indFVars : Array Expr) : MetaM (Nat × List InductiveType) := do
  let masks ← indTypes.mapM (computeFixedIndexBitMask numParams · indFVars)
  if masks.all fun mask => !mask.contains true then
    return (numParams, indTypes.toList)
  -- We process just a non-fixed prefix of the indices for now. Reason: we don't want to change the order.
  -- TODO: extend it in the future. For example, it should be reasonable to change
  -- the order of indices generated by the auto implicit feature.
  let mask := masks[0]
  forallBoundedTelescope indTypes[0].type numParams fun params type => do
    let otherTypes ← indTypes[1:].toArray.mapM fun indType => do whnfD (← instantiateForall indType.type params)
    let ctorTypes ← indTypes.toList.mapM fun indType => indType.ctors.mapM fun ctor => do whnfD (← instantiateForall ctor.type params)
    let typesToCheck := otherTypes.toList ++ ctorTypes.join
    let rec go (i : Nat) (typesToCheck : List Expr) : MetaM Nat := do
      if i < mask.size then
        if !masks.all fun mask => i < mask.size && mask[i] then
           return i
        if !type.isForall then
          return i
        let paramType := type.bindingDomain!
        if !(← typesToCheck.allM fun type => isDomainDefEq type paramType) then
          return i
        withLocalDeclD `a paramType fun paramNew => do
          let typesToCheck ← typesToCheck.mapM fun type => whnfD (type.bindingBody!.instantiate1 paramNew)
          go (i+1) typesToCheck
      else
        return i
    return (← go numParams typesToCheck, indTypes.toList)

private def updateParams (vars : Array Expr) (indTypes : List InductiveType) : TermElabM (List InductiveType) :=
  indTypes.mapM fun indType => do
    let type ← mkForallFVars vars indType.type
    let ctors ← indType.ctors.mapM fun ctor => do
      let ctorType ← mkForallFVars vars ctor.type
      pure { ctor with type := ctorType }
    pure { indType with type := type, ctors := ctors }

private def collectLevelParamsInInductive (indTypes : List InductiveType) : Array Name := Id.run <| do
  let mut usedParams : CollectLevelParams.State := {}
  for indType in indTypes do
    usedParams := collectLevelParams usedParams indType.type
    for ctor in indType.ctors do
      usedParams := collectLevelParams usedParams ctor.type
  return usedParams.params

private def mkIndFVar2Const (views : Array InductiveView) (indFVars : Array Expr) (levelNames : List Name) : ExprMap Expr := Id.run <| do
  let levelParams := levelNames.map mkLevelParam;
  let mut m : ExprMap Expr := {}
  for i in [:views.size] do
    let view    := views[i]
    let indFVar := indFVars[i]
    m := m.insert indFVar (mkConst view.declName levelParams)
  return m

/- Remark: `numVars <= numParams`. `numVars` is the number of context `variables` used in the inductive declaration,
   and `numParams` is `numVars` + number of explicit parameters provided in the declaration. -/
private def replaceIndFVarsWithConsts (views : Array InductiveView) (indFVars : Array Expr) (levelNames : List Name)
    (numVars : Nat) (numParams : Nat) (indTypes : List InductiveType) : TermElabM (List InductiveType) :=
  let indFVar2Const := mkIndFVar2Const views indFVars levelNames
  indTypes.mapM fun indType => do
    let ctors ← indType.ctors.mapM fun ctor => do
      let type ← forallBoundedTelescope ctor.type numParams fun params type => do
        let type := type.replace fun e =>
          if !e.isFVar then
            none
          else match indFVar2Const.find? e with
            | none   => none
            | some c => mkAppN c (params.extract 0 numVars)
        mkForallFVars params type
      pure { ctor with type := type }
    pure { indType with ctors := ctors }

abbrev Ctor2InferMod := Std.HashMap Name Bool

private def mkCtor2InferMod (views : Array InductiveView) : Ctor2InferMod := Id.run <| do
  let mut m := {}
  for view in views do
    for ctorView in view.ctors do
      m := m.insert ctorView.declName ctorView.inferMod
  return m

private def applyInferMod (views : Array InductiveView) (numParams : Nat) (indTypes : List InductiveType) : List InductiveType :=
  let ctor2InferMod := mkCtor2InferMod views
  indTypes.map fun indType =>
    let ctors := indType.ctors.map fun ctor =>
      let inferMod := ctor2InferMod.find! ctor.name -- true if `{}` was used
      let ctorType := ctor.type.inferImplicit numParams !inferMod
      { ctor with type := ctorType }
    { indType with ctors := ctors }

def Constructor.dump (ctor : Constructor) : String := 
  s!"{ctor.name} : {ctor.type}"

def InductiveType.dump (indType : InductiveType) : String :=
  s!"{indType.name} : {indType.type}\n" 
    ++ indType.ctors.foldl (· ++ "  " ++ Constructor.dump · ++ "\n") ""


/-
  A modified version of `mkInductiveDecl`, which performs the same elaborations and checks, but
  returns the elaborated declaration as a `DataDecl`, instead of adding it to the environment
  as an inductive declaration. Also omits the auxiliary constructions.
-/
def mkDataDecl  (vars : Array Expr) (view0 : InductiveView) : TermElabM DataDecl := do
  let views := #[view0]
  let scopeLevelNames ← Term.getLevelNames
  -- checkLevelNames views
  let allUserLevelNames := view0.levelNames
  let isUnsafe          := view0.modifiers.isUnsafe
  withRef view0.ref <| Term.withLevelNames allUserLevelNames do
    let rs ← elabHeader views      
    withInductiveLocalDecls rs fun params indFVars => do
      let mut indTypesArray := #[]
      let mut deadParamsSet := Std.HashSet.empty
      for i in [:views.size] do
        let indFVar := indFVars[i]
        let r       := rs[i]

        if (← isInductiveFamily params.size indFVar) then
          throwErrorAt view0.ref "Inductive families are not supported"

        let type  ← mkForallFVars params r.type
        let ⟨ctors, deadParams⟩ ← elabCtors indFVars indFVar params r
        let indType : InductiveType := { 
                          name := r.view.declName, 
                          type := type,
                          ctors := ctors            
                  }
        indTypesArray := indTypesArray.push indType
        for p in deadParams do
          deadParamsSet := deadParamsSet.insert p
        
      Term.synthesizeSyntheticMVarsNoPostponing
      let (numExplicitParams, indTypes) ← fixedIndicesToParams params.size indTypesArray indFVars
      let u ← getResultingUniverse indTypes
      let inferLevel ← shouldInferResultUniverse u
      withUsed vars indTypes fun vars => do
        let numVars   := vars.size
        let numParams := numVars + numExplicitParams
        let indTypes ← updateParams vars indTypes
        let indTypes ← levelMVarToParam indTypes
        let indTypes ← if inferLevel then updateResultingUniverse numParams indTypes else checkResultingUniverses indTypes; pure indTypes
        let usedLevelNames := collectLevelParamsInInductive indTypes
        match sortDeclLevelParams scopeLevelNames allUserLevelNames usedLevelNames with
        | Except.error msg      => throwError msg
        | Except.ok levelParams => do          
          let indTypes ← replaceIndFVarsWithConsts views indFVars levelParams numVars numParams indTypes
          let indTypes := applyInferMod views numParams indTypes

          let deadParams := deadParamsSet.toList

          let decl ← match indTypes with
           | [indType] => forallTelescopeReducing indType.type fun argTypes _ => do
                              let withTypes := List.zip deadParams argTypes.toList
                              let stxList : List Syntax := match view0.binders with
                                | Syntax.missing => []
                                | _ => []
                              let withSyntax := List.zip withTypes stxList; 
                              let deadParams := withSyntax.filter fun ((param, _), _) => deadParams.contains param
                              let deadParams := deadParams.map fun ((name, type), stx) 
                                => ⟨name, type, stx⟩
                              trace[Meta.debug] "deadParams: {repr deadParams}"
                              pure $ DataDecl.mk levelParams numParams (DataType.mk indType) view0 isUnsafe deadParams
            | _         => throwError "Found more than 1 inductive type"
          Term.ensureNoUnassignedMVars decl.asInductDecl
          pure decl
          /- TODO: see what the following code does (presumably something with pop-up info?)

          withSaveInfoContext do  -- save new env
            for view in views do
              Term.addTermInfo view.ref[1] (← mkConstWithLevelParams view.declName) (isBinder := true)
              for ctor in view.ctors do
                Term.addTermInfo ctor.ref[2] (← mkConstWithLevelParams ctor.declName) (isBinder := true)
              -- We need to invoke `applyAttributes` because `class` is implemented as an attribute.
              Term.applyAttributesAt view.declName view.modifiers.attrs AttributeApplicationTime.afterTypeChecking
          -/
end

end Internals