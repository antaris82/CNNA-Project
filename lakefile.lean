import Lake
open Lake DSL

package «CNNA» where

@[default_target]
lean_lib «CNNA» where
  srcDir := "Repository/repo_snapshot"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"
