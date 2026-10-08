# Hermitian Categories in Lean 4

[![Lean Action CI](https://github.com/wpolitarczyk/lean-HermitianCategories/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/wpolitarczyk/lean-HermitianCategories/actions/workflows/lean_action_ci.yml)

This repository develops a Lean 4 formalization of **Hermitian categories** (categories with duality), sesquilinear and λ-Hermitian forms, and functors compatible with duality. It also includes explicit Tate cohomology constructions for commutative rings with involution.

**Documentation:** [Browse the project documentation](https://wpolitarczyk.github.io/lean-HermitianCategories/docs/).

## Overview

A Hermitian category is a category $\mathcal{C}$ equipped with a contravariant duality functor $ D \colon \mathcal{C}^{\text{op}} \to \mathcal{C} $, a natural isomorphism $ \eta \colon \text{Id}_{\mathcal{C}} \cong D^2 $, and a coherence condition $ D(\eta_X) \circ \eta_{D(X)} = \text{id}_{D(X)} $.

The current formalization includes:

- **Sesquilinear forms:** `Sesq M` is the morphism space $M \to D(M)$, with an abelian group structure when the category is preadditive.
- **Adjoints and λ-Hermitian forms:** the adjoint operation `formDual` is involutive. For a norm-one unit $\lambda$, the condition is $h^\dagger = \lambda \cdot h$. Under the specified additivity and linearity assumptions, these forms constitute an additive subgroup; `StarLinearDuality` expresses conjugate-linearity of the duality.
- **Nonsingular objects and isometries:** `HermitianObject` packages a λ-Hermitian form whose underlying morphism is an isomorphism. `HermitianFormCat` names the resulting category, with invertible form-preserving morphisms as its isometries.
- **Comparisons of dualities:** `DualityComparison` supplies a natural comparison isomorphism; `DualityPreservingFunctor` additionally requires ordinary double-dual coherence. `mapSesqForms` needs only the comparison, and `mapSesqFormsHom` packages transport as an additive homomorphism when the functor is additive.
- **Transport of Hermitian forms:** with the stated linearity assumptions and scalar-dependent compatibility `HermitianFunctor R functor hf eta`, `mapHermitianForms` sends λ-Hermitian forms to `(eta * lam)`-Hermitian forms. `mapHermitianFormsHom` gives the additive homomorphism, and `functorHermitianCategories` gives the induced functor on nonsingular Hermitian objects and isometries.
- **Scaling:** `scalingFunctorCat R s` equips the identity functor with comparison components `s • 𝟙`. Its induced `scalingHermitianCategories R s lam` scales forms by `s⁻¹`, changes their parameter to `(scalingParameter R s * lam)`, where `scalingParameter R s = s * star (s⁻¹)`, and leaves underlying isometry morphisms unchanged.
- **Tate cohomology:** additive and multiplicative cycle/boundary presentations in degrees zero and one. The multiplicative constructions use the unit group of the ring. A generalized half-unit $r + r^* = 1$ implies vanishing of both additive groups.

## Project Layout

| Module | Contents |
| --- | --- |
| [Basic.lean](HermitianCategories/Basic.lean) | Categories with duality, sesquilinear forms, duality preserving functors, and additive transport of forms. |
| [TateCohomology.lean](HermitianCategories/TateCohomology.lean) | Cycles, boundaries, quotient groups, generalized half-units, and the norm-one unit subgroup `Z1Mul`. |
| [HermitianForms.lean](HermitianCategories/HermitianForms.lean) | Adjoints, λ-Hermitian forms, nonsingular objects, isometries, transport by Hermitian functors, and scaling. Imports both modules above. |
| [HermitianCategories.lean](HermitianCategories.lean) | Library entry point importing all three modules. |

To use the full library:

```lean
import HermitianCategories
```

## Work in Progress and TODOs

The concrete Hermitian structures below are planned and are **not yet implemented**:

- [ ] **Finitely generated projective modules:** construct the Hermitian structure from $P \mapsto Hom_R(P,R)$, with the scalar action adjusted for the ring involution, and prove the double-dual isomorphism and coherence.
- [ ] **Finite abelian groups:** construct the Hermitian structure from Pontryagin duality, for example $A \mapsto Hom(A,\mathbb{Q}/\mathbb{Z})$, and prove the double-dual isomorphism and coherence.

Further work on functors:

- [ ] Establish composition properties of Hermitian functors.

`HermitianFunctor` imposes scalar-dependent compatibility on a `DualityComparison`; ordinary coherence is not an additional prerequisite for this transport. To use an ordinary `DualityPreservingFunctor` with the transport constructions, pass its `.toDualityComparison` field.

## Development Environment

The project pins **Lean 4.34.1** in `lean-toolchain` and **Mathlib v4.34.1** in `lakefile.toml`. It can be developed locally or using the supplied VS Code Dev Container.

### Running with Docker

With Docker running:

1. Clone this repository to your local machine.
2. Open the cloned folder in VS Code.
3. Install the **Dev Containers** extension (`ms-vscode-remote.remote-containers`).
4. When prompted (or by pressing `Cmd+Shift+P` / `Ctrl+Shift+P` and typing **Dev Containers: Reopen in Container**), reopen the project in the container.

The container installs the Lean extension and runs `lake update` followed by `lake exe cache get` upon creation. Once setup finishes, run `lake build` in its terminal.

### Running Locally (Without Docker)

Install [elan](https://github.com/leanprover/elan), then run the following from the repository root to download cached Mathlib build artifacts and build the library:

```bash
lake exe cache get
lake build
```

The checked-in `lake-manifest.json` records dependency revisions. Use `lake update` when intentionally refreshing dependency resolution.

The default build target imports all project modules through `HermitianCategories.lean`. GitHub Actions builds the project on pushes, pull requests, and manual runs. After a successful build on a push to `master`, a separate job generates the API documentation and publishes it to GitHub Pages. Documentation deployments run one at a time.
