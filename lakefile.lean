import Lake
open System Lake DSL

package ETHIsFalse where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- CSLib at its last Lean v4.34 commit (2026-09-15, "bump toolchain to v4.34.0"), unmodified.
require cslib from git
  "https://github.com/leanprover/cslib" @ "990e65a685bed413f43b139db900a36ad5322a10"

-- Mathlib v4.34.1, the version OpenAI's proof is pinned to; declared last so it is resolved first.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

/-- OpenAI's proof (`openai/math`, `lean/OAI/Algorithms/SubexponentialSAT`), unmodified. -/
lean_lib OAI where
  srcDir := "OpenAI"
  roots := #[`OAI.Algorithms.SubexponentialSAT.Main]
  globs := #[.andSubmodules `OAI.Algorithms.SubexponentialSAT]

@[default_target]
lean_lib ETHIsFalse where
  roots := #[`ETHIsFalse.Main]
  globs := #[.submodules `ETHIsFalse]
