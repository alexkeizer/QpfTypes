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
