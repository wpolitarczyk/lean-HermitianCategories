import HermitianCategories.Basic
import HermitianCategories.HermitianForms
import HermitianCategories.TateCohomology

/-!
# HermitianCategories library entry point

Importing this module exposes the categorical foundations and duality preserving
functors in `Basic`, the cycle/boundary constructions in `TateCohomology`, and
the category of nonsingular λ-Hermitian forms in `HermitianForms`.

`HermitianForms` depends on both foundational modules. Keep the project's modules
reachable from this entry point so the default library build checks them.
-/
