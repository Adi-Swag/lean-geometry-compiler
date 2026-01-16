import Lake
open Lake DSL

package «geometry_prover» where
  -- package configuration if needed

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- Main library: treat the whole repo root as the Lean source tree
@[default_target]
lean_lib «GeometryProver» where
  srcDir := "."

-- Library that exposes UniGeo.* modules from informal_DSL/UniGeo
lean_lib «UniGeo» where
  srcDir := "informal_DSL"

-- Existing executable
lean_exe «geometry_prover» where
  root := `Main

-- E3 semantic checker executable: entrypoint at E3/Engine/Main.lean
lean_exe e3_checker where
  root := `E3.Engine.Main
