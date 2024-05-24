import Lake
open Lake DSL

package «Lean4Playground» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.7.0"

require scilean from git
  "https://github.com/lecopivo/SciLean" @ "af67d94b6cc276ec74bfb22b684a0fcdbe4a6c9c"

@[default_target]
lean_lib «Lean4Playground» where
  -- add any library configuration options here
