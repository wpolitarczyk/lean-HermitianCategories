# Changelog

## 0.2.0 — 2026-10-19

Refactor the abstract Hermitian-form framework to reuse existing proofs and
Mathlib constructions. Lean and Mathlib remain pinned to version 4.34.1.

### Changes

- Derive the scaling equivalence from the general transport equivalence theorem.
- Reuse adjoint lemmas in the subgroup of Hermitian forms and extract
  `compIsIsometry` for the category instance.
- Use `asIso` to construct isomorphisms from isometries.
- Move `mapSesqForms_injective` and `mapSesqForms_pullback` into `Basic`, and
  reuse transport lemmas for nonsingularity and form preservation.
- Add simplification lemmas for identity and composite duality-comparison
  components, identity transport, and adjoints of pullbacks.
- Bundle additive trace/difference and multiplicative norm/difference maps as
  homomorphisms. Define Tate cycles as kernels and boundaries as ranges, with
  eight membership lemmas recovering the original predicates.
- Rename the existing Apache 2.0 license file from `License` to `LICENSE`,
  matching the source headers and documentation links.

### Migration notes

- `scalingFunctorCompIso` is now `noncomputable`: `asIso` supplies its inverse.
  The forward components are still identity isometries, but inverse components
  no longer reduce definitionally to the previous explicit construction.
- Tate subgroup membership has a different definitional representation. Use
  `mem_Z0Add`, `mem_Z1Add`, `mem_B0Add`, `mem_B1Add` and their multiplicative
  counterparts instead of relying on unfolding the subgroup definitions.
- Identity transport and `formDual_pullback` now participate in `simp`.
- The mathematical statements of the existing main results are preserved.
