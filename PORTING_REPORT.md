# Lean 4 Porting Report

## Completed in this pass
- `src/Grammars/Classes/ContextSensitive/Basics/Inclusion.lean`
- `src/Grammars/Classes/ContextFree/Basics/Inclusion.lean`
- `src/Grammars/Classes/ContextFree/ClosureProperties/Bijection.lean`
- `src/Grammars/Classes/ContextFree/ClosureProperties/Permutation.lean`
- `src/Grammars/Classes/ContextFree/ClosureProperties/Reverse.lean`
- `src/Grammars/Utilities/WrittenByOthers/ListTakeJoin.lean`
- `src/Grammars/Classes/ContextFree/Basics/Elementary.lean`
- `src/Grammars/Classes/ContextFree/Basics/Lifting.lean`
- `src/Grammars/Classes/Unrestricted/Basics/Lifting.lean`
- `src/Grammars/Classes/Unrestricted/NormalForms/Kuroda.lean` (syntax only; theorem still `sorry`)

## Outstanding build blockers
These files still fail `lake build` with Lean 3 syntax or missing API ports:
- `src/Grammars/Classes/ContextFree/Basics/Elementary.lean`
- `src/Grammars/Classes/Unrestricted/Basics/Lifting.lean`
- `src/Grammars/Classes/Unrestricted/ClosureProperties/Reverse.lean`
  - similar Lean 3 syntax updates needed
- `src/Grammars/Classes/Unrestricted/ClosureProperties/Concatenation.lean`
  - extensive Lean 3 syntax, `List.nthLe`, `List.forall₂`, and missing identifiers

## Known sorries
- `src/Grammars/Classes/ContextFree/Basics/Pumping.lean` (`CF_pumping`)
- `src/Grammars/Classes/Unrestricted/NormalForms/Kuroda.lean` (`kuroda_grammar_always_exists`)

## Warnings worth cleaning up later
- Unused simp args in `src/Grammars/Classes/ContextFree/ClosureProperties/Bijection.lean`
- Unused simp args in `src/Grammars/Classes/ContextFree/ClosureProperties/Reverse.lean`
- Unused simp args and minor lints in `src/Grammars/Classes/ContextFree/Basics/Lifting.lean`
- Unused variable warning in `src/Grammars/Classes/Unrestricted/Basics/Lifting.lean`
- Deprecated `structure ... :=` and `variables` warnings in several definition files
