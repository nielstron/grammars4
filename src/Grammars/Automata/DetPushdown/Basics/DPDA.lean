/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Grammars.Automata.Pushdown.Basics.PDA

/-! # Deterministic Pushdown Automata (DPDAs)

This file introduces deterministic pushdown automata (DPDAs).

The embedding of DPDAs into nondeterministic PDAs lives in
`Grammars.Automata.DetPushdown.Basics.Inclusion`.
Complement-closure results live in
`Grammars.Automata.DetPushdown.ClosureProperties.Complement`.
-/

/-- A **Deterministic Pushdown Automaton (DPDA)** over state type `Q`,
    input alphabet `T`, and stack alphabet `S`.

    The key difference from a (nondeterministic) PDA is that the transition functions
    return `Option` values instead of `Set` values, enforcing at most one transition
    per configuration. The `no_mixed` field additionally requires that ε-transitions
    and input-reading transitions are mutually exclusive for each `(state, stack-top)` pair.

    **Determinism guarantee.** Given a configuration `(q, a :: w, Z :: γ)`:
    - If `M.epsilon_transition q Z = some (p, β)`, then the unique possible move is
      to go to `(p, a :: w, β ++ γ)` (the `no_mixed` condition ensures no input-reading
      transition is available).
    - Otherwise, if `M.transition q a Z = some (p, β)`, the unique possible move is
      `(p, w, β ++ γ)`.
    - If neither transition is defined, the machine is stuck (halts). -/
structure DPDA (Q T S : Type) [Fintype Q] [Fintype T] [Fintype S] where
  /-- Initial state -/
  initial_state : Q
  /-- Initial stack symbol -/
  start_symbol : S
  /-- Set of accepting (final) states -/
  final_states : Set Q
  /-- Transition on reading input symbol `a` with stack top `Z`.
      Returns `some (p, β)` where `p` is the new state and `β` replaces `Z` on the stack,
      or `none` if no transition is defined. -/
  transition : Q → T → S → Option (Q × List S)
  /-- ε-transition (no input consumed) with stack top `Z`.
      Returns `some (p, β)` where `p` is the new state and `β` replaces `Z` on the stack,
      or `none` if no transition is defined. -/
  epsilon_transition : Q → S → Option (Q × List S)
  /-- **Determinism constraint**: if an ε-transition is defined for `(q, Z)`, then
      no input-reading transition is defined for `(q, a, Z)` for any input symbol `a`. -/
  no_mixed : ∀ q Z, epsilon_transition q Z ≠ none → ∀ a, transition q a Z = none

namespace DPDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- Embed a DPDA into the nondeterministic PDA framework by converting each `Option`
    transition to the corresponding singleton or empty set. -/
noncomputable def toPDA (M : DPDA Q T S) : PDA Q T S where
  initial_state := M.initial_state
  start_symbol := M.start_symbol
  final_states := M.final_states
  transition_fun q a Z :=
    match M.transition q a Z with
    | some p => {p}
    | none => ∅
  transition_fun' q Z :=
    match M.epsilon_transition q Z with
    | some p => {p}
    | none => ∅
  finite q a Z := by
    cases M.transition q a Z with
    | none => exact Set.toFinite ∅
    | some p => exact Set.toFinite {p}
  finite' q Z := by
    cases M.epsilon_transition q Z with
    | none => exact Set.toFinite ∅
    | some p => exact Set.toFinite {p}

/-- Language accepted by a DPDA via **final-state acceptance**:
    a word `w` is accepted iff the DPDA, starting from its initial configuration,
    can reach a configuration with empty input and an accepting state
    (with any remaining stack contents). -/
def acceptsByFinalState (M : DPDA Q T S) : Language T :=
  M.toPDA.acceptsByFinalState

/-- A DPDA **decides every input** if:
    1. **Totality**: for each word `w`, the DPDA can reach some configuration with
       empty input from the initial configuration.
    2. **Acceptance consistency**: all reachable empty-input configurations for a
       given word `w` agree on whether the state is accepting or not. -/
def DecidesEveryInput (M : DPDA Q T S) : Prop :=
  (∀ w : List T, ∃ q γ, @PDA.Reaches Q T S _ _ _ M.toPDA
    ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q, [], γ⟩) ∧
  (∀ (w : List T) (q₁ q₂ : Q) (γ₁ γ₂ : List S),
    @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q₁, [], γ₁⟩ →
    @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q₂, [], γ₂⟩ →
    (q₁ ∈ M.final_states ↔ q₂ ∈ M.final_states))


end DPDA
