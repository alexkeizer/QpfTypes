
import Lean
import Lean.Parser.Term

import Qpf.Macro.Data.Replace

open Lean Meta


open Parser
private partial def countVarOccurencesAux (r : Replace) (acc : Array Nat) : Syntax → Array Nat
  | Syntax.node _ ``Term.arrow #[arg, arrow, tail] =>     
      -- NOTE: `indexOf` return an index one-past-the-end of `r.vars` if it cant find the index
      let i := r.vars.indexOf arg.getId

      -- dbg_trace "{r.expr}.indexOf {arg} == {i}"
      -- dbg_trace "pre:  {acc}"
      let acc := acc.set! i (acc[i] + 1)
      -- dbg_trace "post: {acc}"
      countVarOccurencesAux r acc tail
  | _ => acc

/-
  For each of the variables added in the `Replace` state, count how many times it is mentioned
  in the given type
-/
def countVarOccurences (r : Replace) (ctor_type?: Option Syntax) : Array Nat :=
  -- array filled with all zeroes
  let acc := (Array.range r.arity).map fun _ => 0
  match ctor_type? with
  | none => acc
  | some t => countVarOccurencesAux r acc t
