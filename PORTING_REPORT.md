# Lean 4 Porting Report

## Completed in this pass
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (re-indented the `complicated_induction` `r₁` branch, replaced remaining `symmetry` uses, removed several `clear_except`s, repaired the `rule_of_rule₁` qualifier, and added explicit casts for the `u'` concatenation)
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (added `List.nth_mem` helper; continued Lean 4 rewrite in `complicated_induction` `h_len` branch, refactoring the `lcth`/`nth_append_right` reasoning and introducing casted `List.nth` steps to keep `rule_of_rule₁` types aligned)
- Started Lean 4 conversion of the `complicated_induction` block in `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (rewrote the outer structure to `by` + `induction`, and began porting the `List.eq_or_mem_of_mem_cons` split; still mid-conversion with Lean 3 syntax remaining).
- No net code changes; started a Lean 4 conversion of `complicated_induction` in `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` but reverted to avoid partial/invalid syntax.
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (added Lean 4 `List.mem_iff_nth_le` lemma to replace missing core lemma)
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (fixed `List.mem_iff_nth_le` binder syntax for Lean 4 parsing)
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (fixed `mem_iff_nth_le` constructor patterns to Lean 4 `List.Mem` shape)
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (replaced `symbol.no_confusion`/`Option.no_confusion` with `cases`-based contradictions)
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (reworked `nthLe_map` usage to avoid extra goals in `init_nt_notin_bef_left`)
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (removed stale `clear` bindings in `complicated_induction` branch)
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (fixed `clear` to avoid dropping `orig_rule` dependencies)
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
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (started cleanup: added `List.nth` compatibility + `nth_*` lemmas, converted early proofs to Lean 4, began `u_eq_take_map_w` updates)
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
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (continued partial port: added `List.nthLe` compatibility and `nthLe_congr`; in-progress rewrites in `u_eq_take_map_w`/`v_eq_drop_map_w`)
- `src/Grammars/Classes/Unrestricted/ClosureProperties/Star.lean` (ported `specific_symbols` and early `construction` definitions plus three inequality lemmas to Lean 4 syntax)
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (Lean 4 fixes in `v_eq_drop_map_w`, updated `sTN₁_of_sTN`/`sTN₂_of_sTN` and `lsTN₁_of_lsTN`/`lsTN₂_of_lsTN` helpers, `filter_map` → `filterMap` conversions, explicit map typing in `h_rhs`)
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (continued Lean 4 port in `in_concatenated_of_in_combined`: rewrote `CF_tran_or_id_of_deri` handling, `only_option` proof, and updated `List.length_eq_zero_iff`/`Eq.symm`/`And` usage)
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (replaced `symbol.no_confusion`/`Sum.no_confusion` with `cases`, switched `.nth` to `List.nth`, and added `c_cast`/`d_cast` casts in the `h_len` contradiction branch)
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` (added `List.nth_append_right` lemma; began Lean 4 rewrite of the `complicated_induction` `r₁` case, converting `let/use/split` to bullets and adding `c_cast`/`d_cast` and `lcth_cast` casts; still mid-port)

## Outstanding build blockers
These files still fail `lake build` with Lean 3 syntax or missing API ports:
- `src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean`
  - `complicated_induction` still contains Lean 3 tactic syntax (`{ ... }`, trailing commas) and now fails parsing around the `have h_len`/`let` blocks in the `List.mem_append` `inl` branch; also needs `List.mem_iff_nth_le` replacement.
  - missing Lean 4 replacements for `List.nth_append_right` and associated `List.nth` rewrite steps in the `h_len` contradiction (line ~914), plus a mismatch between `c_cast`/`d_cast` and the original `c ++ ... ++ d` `nth` target in the rewrite step.
  - `cases orig_in` still lacks a proper `inr` branch structure (Lean 4 parser error near the `let d'` block; `Alternative inr has not been provided`).
  - `complicated_induction` `r₁` branch still has Lean 4 tactic-mode issues: `have`/`let` in tactic blocks causing `unexpected token 'have'`, unresolved casts between `c`/`d` and `c_cast`/`d_cast`, and `List.nth_mem` missing (needs a replacement lemma for `List.nth`/`Option` membership).
  - `complicated_induction` `r₁` branch still failing in the `h_len` contradiction subproof: `lcth_cast` rewrite to `some` is not yet lining up with the `clength`/`clength_combined` statement, and the `c ++ symbol.nonterminal ... :: d` type mismatch (combined vs Option) still triggers HAppend errors.
  - `v_eq_drop_map_w` still failing in the `terminal` case (map/drop to `nthLe` equality, proof irrelevance cleanup, and `symbol.terminal` type ascriptions)
  - `self_of_lsTN₁`/`self_of_lsTN₂` still Lean 3 (`List.filter_map_map`/`List.filter_map_some`) and `List.filter_map` → `List.filterMap` rewrites pending
  - remaining parser fixes around `:=` vs `=>` in equation-style defs
  - downstream errors in `in_concatenated_of_in_combined` and `CF_of_CF_c_CF` remain after `v_eq_drop_map_w`/`self_of_lsTN₁/₂` are fixed
  - `in_concatenated_of_in_combined` still contains large Lean 3 tactic blocks (commas/braces/`rename`/`exfalso`) and needs a full Lean 4 syntax pass, especially `complicated_induction`
  - remaining errors in `CF_of_CF_c_CF` include `Set.eq_of_subSetOf_subset` and `Language` proof elaboration in the final subset arguments
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
- `lean build src/Grammars/Classes/ContextFree/ClosureProperties/Union.lean` fails with `Expected exactly one file name` (Lean CLI expects a single file argument; `lake build` succeeds for file checks).
- `lake build src/Grammars/Classes/ContextFree/ClosureProperties/Concatenation.lean` still fails in `complicated_induction` (remaining `clear_except` cleanup, a `HAppend` type mismatch around `u'` concatenation, and multiple unsolved goals in the `r₁`/`r₂` cases), plus downstream theorem errors around lines 1603+.
