# Hermitian Categories in Lean 4

[![Lean Action CI](https://github.com/wpolitarczyk/lean-HermitianCategories/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/wpolitarczyk/lean-HermitianCategories/actions/workflows/lean_action_ci.yml)

This repository develops a Lean 4 formalization of **Hermitian categories** (categories with duality), sesquilinear and λ-Hermitian forms, and functors compatible with duality. It also includes explicit Tate cohomology constructions for commutative rings with involution.

The **abstract Hermitian-form framework is complete for this milestone**: it includes nonsingular forms and isometries, transport along compatible functors, and a proof that scaling by a unit induces an equivalence of the corresponding categories of Hermitian forms.

**Documentation:** [Browse the project documentation](https://wpolitarczyk.github.io/lean-HermitianCategories/docs/).

## Overview

A Hermitian category is a category $`\mathcal{C}`$ equipped with a contravariant duality functor $`D \colon \mathcal{C}^{\text{op}} \to \mathcal{C}`$, a natural isomorphism $`\eta \colon \text{Id}_{\mathcal{C}} \cong D^2`$, and a coherence condition $`D(\eta_X) \circ \eta_{D(X)} = \text{id}_{D(X)}`$.

The current formalization includes:

- **Sesquilinear forms:** `Sesq M` is the morphism space $`M \to D(M)`$, with an abelian group structure when the category is preadditive.
- **Adjoints and λ-Hermitian forms:** the adjoint operation `formDual` is involutive. For a norm-one unit $`\lambda`$, the condition is $`h^\dagger = \lambda \cdot h`$. Under the specified additivity and linearity assumptions, these forms constitute an additive subgroup; `StarLinearDuality` expresses conjugate-linearity of the duality.
- **Nonsingular objects and isometries:** `HermitianObject` packages a λ-Hermitian form whose underlying morphism is an isomorphism. `HermitianFormCat` names the resulting category, with invertible form-preserving morphisms as its isometries. Inverse isometries give this category a `Groupoid` instance.
- **Comparisons of dualities:** `DualityComparison` supplies a natural comparison isomorphism with forward components $`F(D_C(M)) \to D_D(F(M))`$; `DualityPreservingFunctor` additionally requires ordinary double-dual coherence. `mapSesqForms` transports a form by composing `F.map h` with the forward comparison, without a coherence assumption. `mapSesqFormsHom` packages transport as an additive homomorphism when the functor is additive.
- **Transport of Hermitian forms:** with the stated linearity assumptions and scalar-dependent compatibility `HermitianFunctor R functor hf eta`, `mapHermitianForms` sends λ-Hermitian forms to `(eta * lam)`-Hermitian forms. `mapHermitianFormsHom` gives the additive homomorphism, and `functorHermitianCategories` gives the induced functor on nonsingular Hermitian objects and isometries.
- **Identity, composition, and equivalences:** transport respects identity and composition on forms, objects, and isometries; the induced functor laws hold after parameter casts. `functorHermitianCategoriesIsEquivalence` proves that a compatible linear equivalence induces an equivalence, bundled by `equivalenceHermitianCategories`.
- **Scaling:** `scalingFunctorCat R s` equips the identity functor with comparison components `s • 𝟙`. Its induced `scalingHermitianCategories R s lam` scales forms by `s`, changes their parameter to `(scalingParameter R s * lam)`, where `scalingParameter R s = star s * s⁻¹`, and leaves underlying isometry morphisms unchanged.
- **Scaling composition and equivalence:** `scalingFunctorCompIso` identifies successive scalings by `s` and `t` with scaling by `t * s`, up to a natural isomorphism and the corresponding parameter cast. `scalingFunctorIsEquivalence` proves that every scaling functor is an equivalence; the proof specializes the general transport equivalence theorem to the identity functor with the scaling comparison.
- **Tate cohomology:** additive and multiplicative cycle/boundary presentations in degrees zero and one. The multiplicative constructions use the unit group of the ring. A generalized half-unit $`r + r^* = 1`$ implies vanishing of both additive groups.

In particular, writing $`\sigma(s) = \overline{s}\,s^{-1}`$, the scaling theorem gives

$$
\mathrm{Herm}_{\lambda}(\mathcal{C})
\simeq
\mathrm{Herm}_{\sigma(s)\lambda}(\mathcal{C}).
$$

Here $`R`$ is a commutative ring with involution, $`s \in R^\times`$, and $`\lambda\overline{\lambda}=1`$. The category $`\mathcal{C}`$ is $`R`$-linear and preadditive, with additive, conjugate-linear duality (`StarLinearDuality`). The scaling functor sends a form $`h`$ to $`sh`$. Scaling by the inverse unit, followed by the appropriate parameter cast, reverses this operation.

`HermitianFunctor` imposes scalar-dependent compatibility on a `DualityComparison`; ordinary coherence is not an additional prerequisite for this transport. To use an ordinary `DualityPreservingFunctor` with the transport constructions, pass its `.toDualityComparison` field.

## Project Layout

| Module | Contents |
| --- | --- |
| [Basic.lean](HermitianCategories/Basic.lean) | Categories with duality, sesquilinear forms, duality preserving functors, and additive transport of forms. |
| [TateCohomology.lean](HermitianCategories/TateCohomology.lean) | Cycles, boundaries, quotient groups, generalized half-units, and the norm-one unit subgroup `Z1Mul`. |
| [HermitianForms.lean](HermitianCategories/HermitianForms.lean) | Adjoints, λ-Hermitian forms, nonsingular objects, inverse isometries, and their groupoid structure. Imports `Basic` and `TateCohomology`. |
| [HermitianFunctors.lean](HermitianCategories/HermitianFunctors.lean) | Hermitian functors, transport and its identity/composition laws, parameter casts, induced equivalences, and scaling. Imports `HermitianForms`. |
| [HermitianCategories.lean](HermitianCategories.lean) | Library entry point importing all four modules. |

To use the full library:

```lean
import HermitianCategories
```

For functor and transport constructions, import `HermitianCategories.HermitianFunctors`
or the full library entry point above. Import `HermitianCategories.HermitianForms`
when only the forms and their groupoid structure are needed.

## Scope and Future Extensions

This milestone treats abstract categories with duality. The following extensions are **not yet implemented** and lie outside its scope:

- **Finitely generated projective modules:** construct the Hermitian structure from $`P \mapsto Hom_R(P,R)`$, with the scalar action adjusted for the ring involution, and prove the double-dual isomorphism and coherence.
- **Finite abelian groups:** construct the Hermitian structure from Pontryagin duality, for example $`A \mapsto Hom(A,\mathbb{Q}/\mathbb{Z})`$, and prove the double-dual isomorphism and coherence.
- **Quadratic forms:** extend the project with a formalization of quadratic forms in Hermitian categories.

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

## Releases and License

The current package version is **0.2.1**. See [CHANGELOG.md](CHANGELOG.md) for
release notes and migration details.

Copyright (c) 2026 Wojciech Politarczyk. Released under the
[Apache License 2.0](LICENSE).
