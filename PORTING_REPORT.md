# Lean 4 Porting Report

## Completed in this pass
- `src/Grammars/Classes/ContextSensitive/Basics/Inclusion.lean`
- `src/Grammars/Classes/ContextFree/Basics/Inclusion.lean`
- `src/Grammars/Classes/ContextFree/ClosureProperties/Bijection.lean`
- `src/Grammars/Classes/ContextFree/ClosureProperties/Union.lean` (syntax + tactic port)
- `src/Grammars/Classes/ContextFree/ClosureProperties/Complement.lean`
- `src/Grammars/Classes/ContextFree/ClosureProperties/Permutation.lean`
- `src/Grammars/Classes/ContextFree/ClosureProperties/Reverse.lean`
- `src/Grammars/Utilities/WrittenByOthers/ListTakeJoin.lean`
- `src/Grammars/Classes/ContextFree/Basics/Elementary.lean`
- `src/Grammars/Classes/ContextFree/Basics/Lifting.lean`
- `src/Grammars/Classes/Unrestricted/Basics/Lifting.lean`
- `src/Grammars/Classes/Unrestricted/ClosureProperties/Reverse.lean`
- `src/Grammars/Classes/Unrestricted/NormalForms/Kuroda.lean` (syntax only; theorem still `sorry`)
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (initial Lean 4 syntax pass started; more fixes needed)

## Outstanding build blockers
These files still fail `lake build` with Lean 3 syntax or missing API ports:
- `src/Grammars/Classes/ContextFree/ClosureProperties/Intersection.lean`
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean`
  - still needs `rw` syntax updates (`rw [List.mem_map]` etc.), `begin` → `by`, and `List.filter_map` → `List.filterMap`
  - remaining parser fixes around `:=` vs `=>` in equation-style defs
- `src/Grammars/Classes/ContextFree/ClosureProperties/Union.lean` (now fails because `Concatenation.lean` fails)
- `src/Grammars/Classes/Unrestricted/ClosureProperties/Concatenation.lean`
- `src/Grammars/Classes/Unrestricted/ClosureProperties/Union.lean`
  - partial port; still many Lean 3 `begin`/`end`, `repeat`, and `rw`/`simp` steps to update
  - remaining `List.nthLe` uses and `List.forall₂` API adjustments (now `List.Forall₂`)
  - pending updates in `easy_direction`, `correspondence_for_terminals`, `unwrapping_nst`, and `very_complicated`

## Known sorries
- `src/Grammars/Classes/ContextFree/Basics/Pumping.lean` (`CF_pumping`)
- `src/Grammars/Classes/Unrestricted/NormalForms/Kuroda.lean` (`kuroda_grammar_always_exists`)

## Warnings worth cleaning up later
- Unused simp args in `src/Grammars/Classes/ContextFree/ClosureProperties/Bijection.lean`
- Unused simp args in `src/Grammars/Classes/ContextFree/ClosureProperties/Reverse.lean`
- Unused simp args and minor lints in `src/Grammars/Classes/ContextFree/Basics/Lifting.lean`
- Unused variable warning in `src/Grammars/Classes/Unrestricted/Basics/Lifting.lean`
- Deprecated `structure ... :=` and `variables` warnings in several definition files
