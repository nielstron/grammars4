/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Grammars.Automata.DetPushdown.Basics.DPDA
import Grammars.Automata.DetPushdown.Basics.Determinism
import Grammars.Automata.DetPushdown.Basics.EpsilonElimination

/-! # Making DPDAs Total

This file constructs a total DPDA from a given DPDA: one that decides every input word.

## Strategy

Given a DPDA `M` (assumed to be ε-loop-free after epsilon elimination), we construct
a new DPDA `M'` that:
1. Adds a **sink state** that reads all remaining input without accepting.
2. Adds a **fresh bottom-of-stack marker** so the stack never becomes empty.
3. Whenever the original DPDA would get stuck (no transition defined), redirects to
   the sink state.

The resulting DPDA processes all input symbols for every word, then halts in either
an accepting or non-accepting state.

## Main definitions

- `DPDA.makeTotal` — the total DPDA construction

## Main results

- `makeTotal_language_eq` — the total DPDA accepts the same language
- `makeTotal_decidesEveryInput` — the total DPDA decides every input
-/

namespace DPDA

open PDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

section MakeTotal

variable (M : DPDA Q T S)

/-- The augmented state type: `none` is the sink (dead) state,
    `some q` corresponds to original state `q`. -/
abbrev TotalState (Q : Type) := Option Q

/-- The augmented stack alphabet: `none` is the fresh bottom-of-stack marker,
    `some Z` corresponds to original stack symbol `Z`. -/
abbrev TotalStack (S : Type) := Option S

/-- Construct a total DPDA from the given DPDA.

    - States are `Option Q`: `some q` for original states, `none` for the sink.
    - Stack symbols are `Option S`: `some Z` for original symbols, `none` for the
      bottom-of-stack marker.
    - The sink state reads all remaining input (one symbol at a time) and does not accept.
    - If the original DPDA would get stuck, we redirect to the sink state.
    - The bottom-of-stack marker ensures the stack is never empty. -/
noncomputable def makeTotal : DPDA (Option Q) T (Option S) where
  initial_state := some M.initial_state
  start_symbol := none  -- bottom-of-stack marker
  final_states := { q | ∃ q' ∈ M.final_states, q = some q' }
  transition := fun oq a oZ =>
    match oq, oZ with
    | none, _ =>
      -- Sink state: read input, stay in sink, keep stack unchanged
      some (none, [oZ])
    | some _, none =>
      -- Original state but stack has only the bottom marker:
      -- original DPDA would be stuck (empty original stack), go to sink
      some (none, [none])
    | some q, some Z =>
      match M.epsilon_transition q Z with
      | some _ => none  -- no_mixed: if eps is available, don't read input
      | none =>
        match M.transition q a Z with
        | some (q', β) => some (some q', β.map some ++ [none])
        | none => some (none, [some Z, none])  -- stuck, go to sink
  epsilon_transition := fun oq oZ =>
    match oq, oZ with
    | some q, some Z =>
      match M.epsilon_transition q Z with
      | some (q', β) => some (some q', β.map some)
      | none => none
    | _, _ => none
  no_mixed := by
    intro oq oZ heps a
    match oq, oZ with
    | none, oZ' =>
      simp only at heps
      exact absurd rfl heps
    | some q, none =>
      simp only at heps
      exact absurd rfl heps
    | some q, some Z =>
      simp only [ne_eq] at heps ⊢
      -- heps tells us epsilon_transition (some q) (some Z) ≠ none
      -- so M.epsilon_transition q Z = some _
      split at heps
      · -- M.epsilon_transition q Z = some _
        rename_i q' β heq
        -- transition for (some q, a, some Z) checks M.epsilon_transition q Z first
        rw [show (match M.epsilon_transition q Z with
          | some _ => none
          | none => match M.transition q a Z with
            | some (q', β) => some (some q', β.map some ++ [none])
            | none => some (none, [some Z, none])) = none from by rw [heq]]
      · exact absurd rfl heps

-- ============================================================================
-- Helper lemmas
-- ============================================================================

/-- The sink state is not an accepting state. -/
lemma makeTotal_sink_not_final : (none : Option Q) ∉ (makeTotal M).final_states := by
  simp [makeTotal]

/-- From the sink state, the DPDA reads all remaining input. -/
lemma makeTotal_sink_reads_all (w : List T) (γ : List (Option S)) (hγ : γ ≠ []) :
    @PDA.Reaches (Option Q) T (Option S) _ _ _
      (makeTotal M).toPDA
      ⟨none, w, γ⟩ ⟨none, [], γ⟩ := by
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | cons a w' ih =>
    obtain ⟨Z, rest, rfl⟩ := List.exists_cons_of_ne_nil hγ
    have h_step : @PDA.Reaches₁ (Option Q) T (Option S) _ _ _
        (makeTotal M).toPDA
        ⟨none, a :: w', Z :: rest⟩ ⟨none, w', Z :: rest⟩ := by
      unfold Reaches₁ step
      left
      exact ⟨none, [Z], by unfold DPDA.toPDA makeTotal; simp, by simp⟩
    exact (Relation.ReflTransGen.single h_step).trans ih

-- ============================================================================
-- Language equivalence
-- ============================================================================

/-- The total DPDA accepts the same language as the original. -/
theorem makeTotal_language_eq :
    (makeTotal M).acceptsByFinalState = M.acceptsByFinalState := by
  sorry

-- ============================================================================
-- Totality (decides every input)
-- ============================================================================

/-- The total DPDA decides every input: for every word, it reaches a configuration
    with empty input, and all such configurations agree on acceptance. -/
theorem makeTotal_decidesEveryInput : (makeTotal M).DecidesEveryInput := by
  sorry

end MakeTotal

end DPDA
