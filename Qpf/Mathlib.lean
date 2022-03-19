-- We don't want to import `Mathlib.Data.List.Perm`, 
-- since it defines a `∼` notation that conflicts with our bisimulation notation
-- Since the default `Mathlib` import contains `Mathlib.Data.List.Perm`, we thus individually 
-- import the parts of Mathlib that we need

-- Tactics
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cache
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Coe
import Mathlib.Tactic.CommandQuote
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Core
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Find
import Mathlib.Tactic.IrreducibleDef
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Lint
import Mathlib.Tactic.Lint.Basic
import Mathlib.Tactic.Lint.Frontend
import Mathlib.Tactic.Lint.Simp
import Mathlib.Tactic.NoMatch
import Mathlib.Tactic.NormCast
import Mathlib.Tactic.NormCast.CoeExt
import Mathlib.Tactic.NormCast.Ext
import Mathlib.Tactic.NormCast.Lemmas
import Mathlib.Tactic.NormCast.Tactic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.OpenPrivate
import Mathlib.Tactic.PermuteGoals
import Mathlib.Tactic.PrintPrefix
import Mathlib.Tactic.RCases
import Mathlib.Tactic.Rename
import Mathlib.Tactic.Replace
import Mathlib.Tactic.RestateAxiom
import Mathlib.Tactic.Ring
import Mathlib.Tactic.RunCmd
import Mathlib.Tactic.RunTac
import Mathlib.Tactic.Sat.FromLRAT
import Mathlib.Tactic.ShowTerm
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Simpa
import Mathlib.Tactic.Simps
import Mathlib.Tactic.SolveByElim
import Mathlib.Tactic.Spread
import Mathlib.Tactic.SudoSetOption
import Mathlib.Tactic.TryThis
import Mathlib.Tactic.Use

