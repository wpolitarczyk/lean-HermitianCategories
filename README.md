# Hermitian Categories in Lean 4

This repository contains a Lean 4 formalization of **Hermitian Categories** (categories with duality), along with key algebraic instances and the construction of sesquilinear forms.

## Overview

A Hermitian category is a category $\mathcal{C}$ equipped with a contravariant duality functor $D : \mathcal{C}^{\text{op}} \to \mathcal{C}$, a natural isomorphism $\eta : \text{Id}_{\mathcal{C}} \cong D^2$, and a symmetric coherence condition $D(\eta_X) \circ \eta_{D(X)} = \text{id}_{D(X)}$. 

This project formalizes the base algebraic typeclass and provides the following concrete instances:
* **Finite Abelian Groups (`FinAb`)**: Hermitian structure induced by Pontryagin duality (using an injective cogenerator like $\mathbb{R}/\mathbb{Z}$ or $\mathbb{Q}/\mathbb{Z}$).
* **Finitely Generated Projective Modules (`ProjFinGen R`)**: Hermitian structure over a commutative ring $R$, induced by the standard Hom-duality $P \mapsto \operatorname{Hom}_R(P,R)$.
* **Sesquilinear Forms**: Definition of the abelian group of sesquilinear forms $S(M) := \operatorname{Hom}_{\mathcal{C}}(M, D(M))$ on objects within preadditive Hermitian categories.

## Development Environment

This project is configured for VS Code's **Dev Containers**, ensuring a perfectly reproducible Lean 4 environment isolated from your local machine.

### Running with Docker (Recommended)
1. Clone this repository to your local machine.
2. Open the cloned folder in VS Code.
3. Install the **Dev Containers** extension (`ms-vscode-remote.remote-containers`).
4. When prompted (or by pressing `Cmd+Shift+P` / `Ctrl+Shift+P` and typing **Dev Containers: Reopen in Container**), reopen the project in the container.

*Note: The container is configured to automatically run `lake exe cache get` upon creation to download the pre-compiled Mathlib binaries, which saves hours of compilation time.*

### Running Locally (Without Docker)
If you prefer to run Lean natively, ensure you have [elan](https://github.com/leanprover/elan) installed, then run the following in your terminal:
```bash
lake update
lake exe cache get
lake build
