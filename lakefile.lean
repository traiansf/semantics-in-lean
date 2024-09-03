import Lake
open Lake DSL

package "SemanticsInLean" where
  -- add package configuration options here

lean_lib «SemanticsInLean» where
  -- add library configuration options here

require "leanprover-community" / "mathlib"

@[default_target]
lean_exe "semanticsinlean" where
  root := `Main
