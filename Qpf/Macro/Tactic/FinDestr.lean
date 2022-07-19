
import Qpf.MathlibPort.Fin2

/-!
  `fin_destr i`, where `i` identifies a local hypothesis of type `Fin2 n` will break the current
  goal into `n` separate goals, where in each `i` is replaced by a concrete `Fin2 n` term
-/

open Lean Syntax Elab Elab.Tactic Meta

def elabFinDestrAux (i_stx : Syntax) : TacticM Unit := do
  let u ← mkFreshLevelMVar;
  let n ← mkFreshExprMVar (mkConst ``Nat) (kind:=MetavarKind.synthetic);
  let finTyp := mkApp (mkConst ``PFin2 [u]) n

  let i ← elabTermEnsuringType i_stx finTyp false;
  Term.synthesizeSyntheticMVarsNoPostponing

  -- dbg_trace n
  -- dbg_trace finTyp

  let n ← match (← getExprMVarAssignment? n.mvarId!) with
  | none    => throwErrorAt i_stx "{i_stx} must be of type `Fin2 0` or `Fin2 (Nat.succ n)`"
  | some v  => whnf v

  -- dbg_trace n

  if let some n := n.natLit? then
    let rec genTactic : Nat → TacticM Syntax
    | 0   =>  `(tactic| cases $i_stx:ident)
    | n+1 => do 
              let tct ← genTactic n
              `(tactic| cases $i_stx:ident; swap; rename_i $i_stx:ident; $tct:tactic)

    -- dbg_trace (←genTactic n)
    evalTactic <|← genTactic n

  else
    let rec genTacticExpr : Expr → TacticM (Option Syntax)
      | Expr.const ``Nat.zero .. => 
        `(tactic| cases $i_stx)

      | Expr.app (Expr.const ``Nat.succ ..) n .. => do
          match ←genTacticExpr n with
          | none      => `(tactic| cases $i_stx:ident)
          | some tct  => `(tactic| cases $i_stx:ident; swap; rename_i $i_stx:ident; $tct:tactic)
      | _ => pure none

    match ←genTacticExpr n with
    | some tct => evalTactic tct
    | none     => throwErrorAt i_stx "{i_stx} must be of type `Fin2 0` or `Fin2 (Nat.succ n)`"



elab "fin_destr_one " i:ident : tactic => do
  withMainContext <|
    elabFinDestrAux i

syntax "fin_destr' " ident* : tactic 
macro_rules
| `(tactic| fin_destr' $i:ident $is:ident*) => `(tactic| fin_destr_one $i <;> dsimp <;> fin_destr' $is:ident*)
| `(tactic| fin_destr') => `(tactic| skip)

syntax "fin_destr " ident* : tactic 
macro_rules
| `(tactic| fin_destr $i:ident $is:ident*) => `(tactic| 
      fin_destr' $i:ident $is:ident* 
      <;> try fin_destr
    )

| `(tactic| fin_destr) => `(tactic| 
      first
      | intro i;  fin_destr i
      | funext i; fin_destr i
  )


syntax "vec_eq " (tactic)? : tactic 
macro_rules
| `(tactic| vec_eq) => `(tactic| vec_eq trivial)
| `(tactic| vec_eq $tct:tactic ) => `(tactic| funext i; fin_destr i <;> $tct:tactic)
