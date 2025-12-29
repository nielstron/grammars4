# Lean 4 Porting Report

## Completed in this pass
- `src/Grammars/Classes/ContextSensitive/ClosureProperties/Concatenation.lean` (Lean 4 syntax pass: `Sum` constructors and `by` blocks)
- `src/Grammars/Classes/Unrestricted/ClosureProperties/Concatenation.lean` (partial Lean 4 cleanup: `begin` removal, `corresponding_symbols` port, early lemma rewrites)
- `src/Grammars/Classes/Unrestricted/ClosureProperties/ConcatenationBonus.lean` (Lean 4 syntax pass for two proofs)
- `src/Grammars/Classes/Unrestricted/ClosureProperties/UnionBonus.lean` (Lean 4 syntax pass for two proofs)
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
- `src/Grammars/Classes/Unrestricted/ClosureProperties/Union.lean` (Lean 4 syntax + proof fixes; builds with warnings)
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
  - heavy Lean 3 syntax cleanup still in progress; many lemmas retain trailing commas and `by { ... }` blocks
  - remaining equation-style defs still need `:=` → `=>` conversions
  - type errors around mixed list concatenations (`List (nst ...)` vs `List (symbol ...)`) to revisit after syntax fixes
  - `and`/`True`/`False` cleanup still needed in a few sections (use Prop-level `And` or `∧`)

## Known sorries
- `src/Grammars/Classes/ContextFree/Basics/Pumping.lean` (`CF_pumping`)
- `src/Grammars/Classes/Unrestricted/NormalForms/Kuroda.lean` (`kuroda_grammar_always_exists`)

## Warnings worth cleaning up later
- Unused simp args in `src/Grammars/Classes/ContextFree/ClosureProperties/Bijection.lean`
- Unused simp args in `src/Grammars/Classes/ContextFree/ClosureProperties/Reverse.lean`
- Unused simp args and minor lints in `src/Grammars/Classes/ContextFree/Basics/Lifting.lean`
- Unused variable warning in `src/Grammars/Classes/Unrestricted/Basics/Lifting.lean`
- Minor simp/lint suggestions in `src/Grammars/Classes/Unrestricted/ClosureProperties/Union.lean`
- Deprecated `structure ... :=` and `variables` warnings in several definition files

## Build/test notes
- `lake build Grammars.Classes.Unrestricted.ClosureProperties.ConcatenationBonus` failed because `src/Grammars/Classes/Unrestricted/ClosureProperties/Concatenation.lean` still has Lean 3 syntax (`begin`/`end`, `:=` vs `=>`) and typeclass issues.
- `lake build Grammars.Classes.ContextSensitive.ClosureProperties.Concatenation` currently fails in `src/Grammars/Classes/Unrestricted/ClosureProperties/Concatenation.lean` due to remaining `begin`/`end` and parser errors.
- `lake build Grammars.Classes.Unrestricted.ClosureProperties.Concatenation` currently fails with many Lean 4 syntax errors (trailing commas, `:=` vs `=>`, `by { ... }`) and a few proof obligations in the `correspondence_for_terminals` and `unwrapping_nst` sections.
