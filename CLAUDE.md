# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

NewPFTypes is a Lean 4 library project to define coinductive types via polynomial functors, with minimal (eventually no) Mathlib dependencies.
More details about the plan for this project can be found in Plan.md and/or TODO.md

## Build Commands

```bash
# Build the library
lake build

# Build and run the executable
lake exe newpftypes

# Clean build artifacts
lake clean
```

## Project Structure

- `NewPFTypes.lean` - Root module that imports all library submodules
- `NewPFTypes/` - Library modules directory (add new modules here)
- `Main.lean` - Executable entry point (imports NewPFTypes library)
- `lakefile.toml` - Lake build configuration

## Lean 4 Version

Uses Lean 4.28.0 (specified in `lean-toolchain`).

## Adding New Modules

1. Create `NewPFTypes/YourModule.lean`
2. Add `import NewPFTypes.YourModule` to `NewPFTypes.lean`

## Porting Mathlib Files (removing Mathlib dependencies)

When porting a file that starts with `import Mathlib.Tactic` or similar, the following substitutions are needed. The goal is to have no Mathlib imports.

### Notation / syntax replacements

| Mathlib | Core Lean 4 replacement | Notes |
| ------- | ----------------------- | ----- |
| `ℕ` | `Nat` | `ℕ` notation requires Mathlib in Lean 4.28.0 |
| `Type*` | `Type _` | Mathlib elaborator macro |
| `Sort*` | `Sort _` | Mathlib elaborator macro |
| `congr_fun h` | `congrFun h` | Lean 4 uses camelCase in core |
| `@[pp_with_univ]` | *(remove)* | Mathlib-only pretty-printing attribute |

### Scoped notation strategy

`scoped[MvFunctor]` (or any external namespace) requires Mathlib. The pattern that works without any imports:

1. Wrap the file content in a local namespace (e.g. `namespace QpfTypes`)
2. Use plain `scoped infixl/infixr/notation ...` — this scopes to the current namespace
3. Users `open QpfTypes` to get the notation

Do NOT use `scoped[NS]` syntax — it is not available in Lean 4.28.0 core.

### Fin2 → Fin

Mathlib's TypeVec used `Fin2` (inductive type). This project uses `Fin` (subtype of `Nat`):

| `Fin2` | `Fin` equivalent |
| ------ | ---------------- |
| `Fin2.fz` | `(0 : Fin (n+1))` |
| `Fin2.fs i` | `i.succ` |
| `Fin2.elim0` | `Fin.elim0` |
| Case split on `Fin2` | `Fin.cases h0 hs i` |
| Structural induction on `Fin2` | `induction i using Fin.succRecOn` |

For **definitions**, prefer plain pattern matching (`| ⟨0, _⟩ =>` / `| ⟨k+1, h⟩ =>`). Use `Fin.cases` only when it significantly shortens the definition — it does give definitional equalities (`Fin.cases h0 hs 0 = h0` and `Fin.cases h0 hs i.succ = hs i` reduce by `rfl`), but plain patterns are clearer.

For **proofs**, use `induction i using Fin.succRecOn` — the motive quantifies over both `n` and `i : Fin n`, so variables typed over `n` are auto-generalized. Apply the IH at `drop α` etc. when types don't auto-unify.

### What IS in core Lean 4 (no imports needed)

- `@[ext]` attribute and `ext` tactic
- `funext`, `simp`, `rfl`, `congr`, `cases`, `refine`, `exact`, `intro`
- `Fin.cases`, `Fin.elim0`, `Fin.succ`, `Fin.cases_zero`, `Fin.cases_succ` (`@[simp]` lemmas)
- `Fin.succRecOn` (in `Init.Data.Fin.Lemmas`)
- `congrFun`, `cast`, `Eq.mp`, `Eq.mpr`
- `Function.comp` (but `Function.uncurry` — check if actually used before importing)

### What requires Mathlib / should be removed

- `register_simp_attr` — may already be declared by Mathlib; just remove the line
- `open MvFunctor` — `MvFunctor` only exists in Mathlib; replace with local namespace strategy above
- QPF-specific definitions (`Subtype_`, `repeatEq`, `PredLast'`, `RelLast'`, `diagSub`, `ofRepeat`) — intentionally excluded from this project
