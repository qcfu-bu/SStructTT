# Substructural Dependent Type Theory
This repository contains the formalization of 
Substructural Dependent Type Theory (SStruct) in [Lean 4](https://lean-lang.org/).

| logic    | contraction | weakening | sort |
| -------- | ----------- | --------- | ---- |
| linear   | no          | no        | L    |
| affine   | no          | yes       | A    |
| relevant | yes         | no        | R    |
| unbound  | yes         | yes       | U    |

## Dependencies
- Lean 4 toolchain (v4.19.0)
- [Mathlib4](https://github.com/leanprover-community/mathlib4) (v4.19.0)

## Build Instructions
1. Fetch cache for Mathlib4 with `lake exec get cache`.
2. Build SStruct with `lake build`.

## Organizational Structure
- **SStructTT/**
  - **Basics/**: Basic definitions (autorewrite system and σ-substitution calculus).
  - **MartinLof/**: Formalization of Martin-Löf Type Theory (axiomatized strong normalization).
  - **SStruct/**
    - **Static/**: Logical level theories. 
    - **Dynamic/**: Program level theories.
    - **Erasure/**:  Erasure soundness theories.
    - **Runtime/**:  Runtime soundness theories
    - `SrtOrder.lean`: Typeclass for sort-orderings.
    - `Syntax.lean`: Abstract syntax of SStruct.
- `SStructTT.lean`: Root module file of project.