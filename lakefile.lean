import Lake
open Lake DSL

package «grammars» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.9.1"

@[default_target]
lean_lib «Grammars» where
  srcDir := "src"
  roots := #[`Grammars]

lean_lib «GrammarsTest» where
  srcDir := "test"
  roots := #[`Grammars.Test]
