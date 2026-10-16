import HermitianCategories.Basic
import HermitianCategories.HermitianForms
import HermitianCategories.HermitianFunctors
import HermitianCategories.TateCohomology
import HermitianCategories.QuadraticForms

/-!
# HermitianCategories library entry point

Importing this module exposes the categorical foundations and duality preserving
functors in `Basic`, the cycle/boundary constructions in `TateCohomology`, and
the groupoid of nonsingular λ-Hermitian forms in `HermitianForms`, and transport,
induced equivalences, and scaling in `HermitianFunctors`.

`HermitianForms` depends on both foundational modules; `HermitianFunctors`
builds on `HermitianForms`. Keep the project's modules
reachable from this entry point so the default library build checks them.
-/



