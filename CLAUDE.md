# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

QPFTypes is a Lean 4 library project to define coinductive types via polynomial functors, with minimal (eventually no) Mathlib dependencies.
More details about the plan for this project can be found in Plan.md and/or TODO.md

## Finding Mathlib Source Files

When looking up Mathlib source files (e.g. to port them), always search in the **project's own lake packages**:

```text
.lake/packages/mathlib/Mathlib/...
```

Do **not** look in other projects' lake packages elsewhere on the filesystem.

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

- `QPFTypes.lean` - Root module that imports all library submodules
- `QPFTypes/` - Library modules directory (add new modules here)
- `Main.lean` - Executable entry point (imports QPFTypes library)
- `lakefile.toml` - Lake build configuration

## Lean 4 Version

Uses Lean 4.28.0 (specified in `lean-toolchain`).

## Adding New Modules

1. Create `QPFTypes/YourModule.lean`
2. Add `import QPFTypes.YourModule` to `QPFTypes.lean`

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

1. Wrap the file content in a local namespace (e.g. `namespace QPFTypes`)
2. Use plain `scoped infixl/infixr/notation ...` — this scopes to the current namespace
3. Users `open QPFTypes` to get the notation

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

### Module system and namespace wrapping

When porting Mathlib files, the following structural changes are needed:

1. **Add QPFTypes namespace wrapper**:
   - Wrap the entire file content in `namespace QPFTypes` / `end QPFTypes`
   - Keep the original namespace (e.g., `MvPFunctor`) nested inside

2. **Adjust imports**:
   - Change `public import Mathlib.X.Y.Z` to local project imports like `import QPFTypes.X.Y.Z`
   - Remove ALL Mathlib imports (the goal is zero Mathlib dependencies)
   - If functionality seems to require Mathlib, check if it's available through already-ported local modules or if it can be replaced with explicit function calls

Example transformation:
```lean
-- Mathlib version:
module
@[expose] public section
namespace MvPFunctor
...
end MvPFunctor

-- Ported version:
namespace QPFTypes
namespace MvPFunctor
...
end MvPFunctor
end QPFTypes
```

### MvFunctor notation: `<$$>` operator

Mathlib's `MvFunctor` typeclass provides the `<$$>` notation for mapping. Since we're eliminating Mathlib dependencies, replace this notation with explicit function calls:

| Mathlib usage | Replacement | Context |
| ------------- | ----------- | ------- |
| `g <$$> x` | `P.wp.map g x` | When mapping over `P.wp` objects |
| `g <$$> x` | `P.map g x` | When mapping over `P` objects |
| `g <$$> P.wMk a f' f` | `P.wMap g (P.wMk a f' f)` | When using the W-type map |
| `MvFunctor.map g ∘ f` | `P.wMap g ∘ f` | In function composition |
| `appendFun g h <$$> x` | `P.map (appendFun g h) x` | Parenthesize the function argument |

**Pattern**: The `<$$>` operator is infix notation for `MvFunctor.map`. When porting:
- Identify what type `x` has to determine which `.map` function to use
- Make the call explicit: `Type.map g x` rather than `g <$$> x`
- If a custom map function exists (like `wMap`), prefer using it for clarity

### Type definitions vs type aliases

Mathlib sometimes defines types as functions with separate typeclass instances. When porting, prefer simpler direct definitions:

**Mathlib pattern**:
```lean
def W (α : TypeVec n) : Type _ := P.wp α
instance mvfunctorW : MvFunctor P.W := by delta MvPFunctor.W; infer_instance
```

**Ported pattern**:
```lean
def W : TypeVec n → Type _ := P.wp.Obj
-- No instance needed if we're not using the typeclass
```

**Rationale**: Since we're eliminating Mathlib dependencies, we don't use the `MvFunctor` typeclass. Simplify type definitions and remove instances that exist only to satisfy typeclass requirements. The actual map functionality is available through the polynomial functor's own `.map` method.

### Proof adjustments for transparency

Some definitions that compute definitionally in Mathlib may require explicit unfolding in the ported version:

**Mathlib version**:
```lean
theorem wRec_eq ... : P.wRec g (P.wMk a f' f) = ... := rfl
```

**Ported version**:
```lean
theorem wRec_eq ... : P.wRec g (P.wMk a f' f) = ... := by
  unfold wRec wMk
  rfl
```

**When to add `unfold`**: If a proof that was just `rfl` in Mathlib fails to typecheck, try adding `unfold` for the relevant definitions before `rfl`.

### Selective theorem porting

Not all theorems from Mathlib need to be ported. Some are only relevant in the full Mathlib context:

- **Port theorems that**:
  - Define core properties of the data structure
  - Are needed for later constructions in this project
  - Establish basic equivalences and computation rules

- **Skip theorems that**:
  - Only exist to satisfy Mathlib-specific typeclass requirements
  - Depend on advanced Mathlib machinery not being ported
  - Are marked as TODO or noted as "used in one place" that's not being ported

Example: `wDest'_wMk'` was omitted from the W-types port (it depends on `split_dropFun_lastFun` which may not be ported yet).
