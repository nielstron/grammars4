import Lake
open Lake DSL

package «grammars» where
  -- add package configuration options here
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0"

require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.26.0"

@[default_target]
lean_lib «Grammars» where
  srcDir := "src"
  roots := #[`Grammars]

lean_lib «GrammarsTest» where
  srcDir := "test"
  roots := #[`Grammars.Test]
