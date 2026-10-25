#!/usr/bin/env bash
set -euo pipefail

# Match docgen-action's isolated docbuild package and toolchain-matched doc-gen4
# dependency, but only build the API documentation: no Pages upload or deploy.
# Use a cold documentation cache to reproduce the failing run's workload.
toolchain=$(cat lean-toolchain)
mkdir -p docbuild
cat > docbuild/lakefile.toml <<EOF
name = "docbuild"
reservoir = false
version = "0.1.0"
packagesDir = "../.lake/packages"

[[require]]
name = "HermitianCategories"
path = "../"

[[require]]
scope = "leanprover"
name = "doc-gen4"
rev = "${toolchain##*:}"
EOF

cd docbuild
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update HermitianCategories
lake build HermitianCategories:docs
