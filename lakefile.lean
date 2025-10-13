import Lake
open Lake DSL

package «geometry_prover» where
  -- add package configuration options here

lean_lib «GeometryProver» where
  -- add library configuration options here

@[default_target]
lean_exe «geometry_prover» where
  root := `Main

-- This is the crucial line that adds mathlib
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
