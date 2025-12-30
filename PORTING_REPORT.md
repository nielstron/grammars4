# Lean 4 Porting Report

## Completed in this pass
- `src/Grammars/Classes/ContextFree/ClosureProperties/Intersection.lean` (ported remaining `begin` blocks in `intersection_inclusions` + `nnyCF_of_CF_i_CF` to `by` style)
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (ported `in_combined_of_in_concatenated` + `CF_of_CF_c_CF` to Lean 4 `by` style)
- `src/Grammars/Classes/ContextSensitive/ClosureProperties/Concatenation.lean` (Lean 4 syntax pass: `Sum` constructors and `by` blocks)
- `src/Grammars/Classes/Unrestricted/ClosureProperties/Concatenation.lean` (partial Lean 4 cleanup: `begin` removal, `corresponding_symbols` port, early lemma rewrites)
- `src/Grammars/Classes/Unrestricted/ClosureProperties/ConcatenationBonus.lean` (Lean 4 syntax pass for two proofs)
- `src/Grammars/Classes/Unrestricted/ClosureProperties/UnionBonus.lean` (Lean 4 syntax pass for two proofs)
- `src/Grammars/Classes/ContextSensitive/Basics/Inclusion.lean`
- `src/Grammars/Classes/ContextFree/Basics/Inclusion.lean`
- `src/Grammars/Classes/ContextFree/ClosureProperties/Bijection.lean`
- `src/Grammars/Classes/ContextFree/ClosureProperties/Union.lean` (syntax + tactic port)
- `src/Grammars/Classes/ContextFree/ClosureProperties/Union.lean` (Lean 4 proof fixes in `in_language_of_in_union`; file now builds)
- `src/Grammars/Classes/ContextFree/ClosureProperties/Complement.lean`
- `src/Grammars/Classes/ContextFree/ClosureProperties/Permutation.lean`
- `src/Grammars/Classes/ContextFree/ClosureProperties/Reverse.lean`
- `src/Grammars/Utilities/WrittenByOthers/ListTakeJoin.lean`
- `src/Grammars/Classes/ContextFree/Basics/Elementary.lean`
- `src/Grammars/Classes/ContextFree/Basics/Lifting.lean`
- `src/Grammars/Classes/Unrestricted/Basics/Lifting.lean`
- `src/Grammars/Classes/Unrestricted/ClosureProperties/Reverse.lean`
- `src/Grammars/Classes/Unrestricted/ClosureProperties/Union.lean` (Lean 4 syntax + proof fixes; builds with warnings)
- `src/Grammars/Classes/Unrestricted/NormalForms/Kuroda.lean` (Lean 4 syntax pass with temporary axiom)
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (initial Lean 4 syntax pass started; more fixes needed)
- `src/Grammars/Classes/ContextFree/Basics/Pumping.lean` (Lean 4 syntax pass with temporary axiom)
- `src/Grammars/Classes/ContextFree/ClosureProperties/Intersection.lean` (partial Lean 4 conversion: `false_of_uvvxyyz`, `notCF_lang_eq_eq`, `CF_lang_eq_any`, `CF_lang_any_eq`, `permut` port, and small helpers)
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (ported `u_eq_take_map_w`, `v_eq_drop_map_w`, `self_of_sTN₁/₂`, `self_of_lsTN₁/₂` to Lean 4 `by` style)
- `src/Grammars/Classes/Unrestricted/ClosureProperties/Star.lean` (ported `specific_symbols` and early `construction` definitions plus three inequality lemmas to Lean 4 syntax)

## Outstanding build blockers
These files still fail `lake build` with Lean 3 syntax or missing API ports:
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean`
  - still needs `rw` syntax updates (`rw [List.mem_map]` etc.), `begin` → `by`, and `List.filter_map` → `List.filterMap`
  - `in_concatenated_of_in_combined` still in Lean 3 block style and needs Lean 4 tactic syntax pass
  - remaining parser fixes around `:=` vs `=>` in equation-style defs
- `src/Grammars/Classes/Unrestricted/ClosureProperties/Concatenation.lean`
  - heavy Lean 3 syntax cleanup still in progress; many lemmas retain trailing commas and `by { ... }` blocks
  - remaining equation-style defs still need `:=` → `=>` conversions
  - type errors around mixed list concatenations (`List (nst ...)` vs `List (symbol ...)`) to revisit after syntax fixes
  - `and`/`True`/`False` cleanup still needed in a few sections (use Prop-level `And` or `∧`)
- `src/Grammars/Classes/Unrestricted/ClosureProperties/Star.lean`
  - still heavy Lean 3 syntax (`begin`/`end`, `sum` namespace, `dec_trivial`) throughout; only `specific_symbols` section updated so far
  - needs `sum.get_left` replacements and `sum` → `Sum` conversions in `short_induction` and later proofs

## Known axioms (need elimination)
- `src/Grammars/Classes/ContextFree/Basics/Pumping.lean` (`cf_pumping_axiom` backing `CF_pumping`)
- `src/Grammars/Classes/Unrestricted/NormalForms/Kuroda.lean` (`kuroda_grammar_always_exists_axiom` backing `kuroda_grammar_always_exists`)

## Warnings worth cleaning up later
- Unused simp args in `src/Grammars/Classes/ContextFree/ClosureProperties/Bijection.lean`
- Unused simp args in `src/Grammars/Classes/ContextFree/ClosureProperties/Reverse.lean`
- Unused simp args and minor lints in `src/Grammars/Classes/ContextFree/Basics/Lifting.lean`
- Unnecessary `simpa` warning in `src/Grammars/Classes/ContextFree/ClosureProperties/Union.lean`
- Unused variable warning in `src/Grammars/Classes/Unrestricted/Basics/Lifting.lean`
- Minor simp/lint suggestions in `src/Grammars/Classes/Unrestricted/ClosureProperties/Union.lean`
- Deprecated `structure ... :=` and `variables` warnings in several definition files

## Build/test notes
- `lake build Grammars.Classes.Unrestricted.ClosureProperties.ConcatenationBonus` failed because `src/Grammars/Classes/Unrestricted/ClosureProperties/Concatenation.lean` still has Lean 3 syntax (`begin`/`end`, `:=` vs `=>`) and typeclass issues.
- `lake build Grammars.Classes.ContextSensitive.ClosureProperties.Concatenation` currently fails in `src/Grammars/Classes/Unrestricted/ClosureProperties/Concatenation.lean` due to remaining `begin`/`end` and parser errors.
- `lake build Grammars.Classes.Unrestricted.ClosureProperties.Concatenation` currently fails with many Lean 4 syntax errors (trailing commas, `:=` vs `=>`, `by { ... }`) and a few proof obligations in the `correspondence_for_terminals` and `unwrapping_nst` sections.
