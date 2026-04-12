import Lake
open Lake DSL

package «touchette-lloyd» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Pin to a specific Mathlib commit for reproducibility.
-- After cloning, run `lake update` then `lake build` to fetch dependencies.
-- You may need to update the lean-toolchain to match Mathlib's:
--   cp lake-packages/mathlib/lean-toolchain .
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib «TouchetteLloyd» where
  srcDir := "."
