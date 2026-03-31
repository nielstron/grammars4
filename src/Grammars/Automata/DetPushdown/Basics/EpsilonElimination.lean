/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Grammars.Automata.DetPushdown.Basics.DPDA
import Grammars.Automata.DetPushdown.Basics.Determinism

/-! # Epsilon-Loop Elimination for DPDAs

This file constructs an equivalent DPDA that never enters an infinite ε-loop.

## Strategy

A DPDA can potentially loop forever on ε-transitions without reading any input.
We eliminate this by augmenting the state with a counter that tracks the number of
consecutive ε-transitions. Since there are `|Q| × |S|` possible `(state, stack-top)`
pairs, after that many consecutive ε-transitions the pigeonhole principle guarantees
a repeated pair, which (by determinism) means an infinite loop. We cut off such loops
by refusing to take ε-transitions once the counter reaches the bound.

## Main definitions

- `DPDA.epsilonBound` — the bound `|Q| × |S|` on consecutive ε-transitions
- `DPDA.elimEpsilonLoops` — the modified DPDA with counter-augmented states

## Main results

- `elimEpsilonLoops_language_eq` — the modified DPDA accepts the same language
-/

namespace DPDA

open PDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- The maximum number of consecutive ε-transitions before a (state, stack-top) pair
    must repeat (by pigeonhole). -/
noncomputable def epsilonBound : ℕ := Fintype.card Q * Fintype.card S

section ElimEpsilonLoops

variable (M : DPDA Q T S)

/-- Construct the ε-loop-free DPDA by augmenting states with an ε-counter. -/
noncomputable def elimEpsilonLoops :
    DPDA (Q × Fin (epsilonBound (Q := Q) (S := S) + 1)) T S where
  initial_state := (M.initial_state, 0)
  start_symbol := M.start_symbol
  final_states := { qs | qs.1 ∈ M.final_states }
  transition := fun qs a Z =>
    match M.transition qs.1 a Z with
    | some (q', β) => some ((q', 0), β)
    | none => none
  epsilon_transition := fun qs Z =>
    if h : qs.2.val < epsilonBound then
      match M.epsilon_transition qs.1 Z with
      | some (q', β) => some ((q', ⟨qs.2.val + 1, by omega⟩), β)
      | none => none
    else
      none
  no_mixed := by
    intro ⟨q, k⟩ Z heps a
    simp only [ne_eq] at heps ⊢
    split at heps
    · rename_i hk
      split at heps
      · rename_i heq
        have : M.epsilon_transition q Z ≠ none := by rw [heq]; exact Option.some_ne_none _
        have := M.no_mixed q Z this a
        simp [this]
      · exact absurd rfl heps
    · exact absurd rfl heps

/-
PROBLEM
============================================================================
Part 1: Projection (augmented → original)
============================================================================

Single-step projection.

PROVIDED SOLUTION
Case split on c₁'s configuration structure. Unfold Reaches₁, step, toPDA, elimEpsilonLoops and case split on match arms.
-/
lemma elimEpsilonLoops_step_projects
    (c₁ c₂ : PDA.conf (elimEpsilonLoops M).toPDA)
    (h : PDA.Reaches₁ c₁ c₂) :
    @PDA.Reaches₁ Q T S _ _ _ M.toPDA
      ⟨c₁.state.1, c₁.input, c₁.stack⟩ ⟨c₂.state.1, c₂.input, c₂.stack⟩ := by
  cases c₁ ; cases c₂ ; simp_all +decide [ DPDA.elimEpsilonLoops ] ;
  rename_i q w γ q' w' γ';
  rcases w with ( _ | ⟨ a, w ⟩ ) <;> rcases γ with ( _ | ⟨ Z, γ ⟩ ) <;> simp_all +decide [ Reaches₁ ];
  · unfold step at h; aesop;
  · unfold step at *;
    unfold DPDA.toPDA at *;
    rcases h : M.epsilon_transition q.1 Z with ( _ | ⟨ p, β ⟩ ) <;> simp_all +decide [ PDA.Reaches₁ ];
    split_ifs at * <;> simp_all +decide [ Set.mem_singleton_iff ];
  · unfold step at * ; aesop;
  · unfold step at *;
    unfold DPDA.toPDA at *;
    cases h' : M.transition q.1 a Z <;> cases h'' : M.epsilon_transition q.1 Z <;> simp +decide [ h', h'' ] at h ⊢;
    · split_ifs at h <;> simp_all +decide [ Set.mem_singleton_iff ];
    · aesop;
    · have := M.no_mixed q.1 Z; aesop;

/-
PROBLEM
Multi-step projection.

PROVIDED SOLUTION
Induction on ReflTransGen. Base: refl. Step: use elimEpsilonLoops_step_projects, compose via tail.
-/
lemma elimEpsilonLoops_projects
    (q q' : Q) (w : List T) (γ γ' : List S)
    (k k' : Fin (epsilonBound (Q := Q) (S := S) + 1))
    (h : @PDA.Reaches _ T S _ _ _
      (elimEpsilonLoops M).toPDA
      ⟨(q, k), w, γ⟩ ⟨(q', k'), [], γ'⟩) :
    @PDA.Reaches Q T S _ _ _ M.toPDA ⟨q, w, γ⟩ ⟨q', [], γ'⟩ := by
  have h_proj : ∀ c₁ c₂ : PDA.conf (M.elimEpsilonLoops.toPDA), PDA.Reaches c₁ c₂ → @PDA.Reaches Q T S _ _ _ M.toPDA ⟨c₁.state.1, c₁.input, c₁.stack⟩ ⟨c₂.state.1, c₂.input, c₂.stack⟩ := by
    intros c₁ c₂ h_reaches
    induction' h_reaches with c₁ c₂ h_step h_ind;
    · constructor;
    · exact Relation.ReflTransGen.tail ‹_› ( by exact? );
  exact h_proj _ _ h

/-
PROBLEM
============================================================================
Part 2: Simulation helpers
============================================================================

Lift an input-reading step. Counter resets to 0.

PROVIDED SOLUTION
Unfold Reaches₁ and step. Show the target is in the left part of the union (input-reading transitions). The augmented DPDA's toPDA.transition_fun (q,k) a Z = {((q',0), β)} because elimEpsilonLoops.transition (q,k) a Z = some ((q',0), β) from ht.
-/
lemma elimEpsilonLoops_lift_input_step
    (q q' : Q) (a : T) (w : List T) (Z : S) (α β : List S)
    (k : Fin (epsilonBound (Q := Q) (S := S) + 1))
    (ht : M.transition q a Z = some (q', β)) :
    @PDA.Reaches₁ _ T S _ _ _
      (elimEpsilonLoops M).toPDA
      ⟨(q, k), a :: w, Z :: α⟩ ⟨(q', 0), w, β ++ α⟩ := by
  convert Set.mem_union_left _ _ using 1;
  unfold DPDA.elimEpsilonLoops;
  unfold DPDA.toPDA; aesop;

/-
PROBLEM
Lift a single ε-step. Counter increments (must be below bound).

PROVIDED SOLUTION
Unfold Reaches₁ and step. The augmented DPDA's epsilon_transition at (q,k) with Z: since hk : k.val < epsilonBound, the if branch is taken. Since ht: M.epsilon_transition q Z = some (q',β), we get some ((q', k+1), β). So transition_fun' = {((q', k+1), β)}.
-/
lemma elimEpsilonLoops_lift_epsilon_step
    (q q' : Q) (w : List T) (Z : S) (α β : List S)
    (k : Fin (epsilonBound (Q := Q) (S := S) + 1))
    (hk : k.val < epsilonBound)
    (ht : M.epsilon_transition q Z = some (q', β)) :
    @PDA.Reaches₁ _ T S _ _ _
      (elimEpsilonLoops M).toPDA
      ⟨(q, k), w, Z :: α⟩ ⟨(q', ⟨k.val + 1, by omega⟩), w, β ++ α⟩ := by
  unfold Reaches₁
  generalize_proofs at *;
  unfold step;
  rcases w with ( _ | ⟨ a, w ⟩ ) <;> simp_all +decide [ DPDA.toPDA ];
  · unfold DPDA.elimEpsilonLoops; aesop;
  · unfold DPDA.elimEpsilonLoops; aesop;

/-
PROBLEM
============================================================================
Part 2b: Pigeonhole bound on consecutive ε-transitions
============================================================================

In a DPDA, an ε-step on empty input with non-empty stack preserves the empty input.
    Moreover the next configuration is fully determined.

PROVIDED SOLUTION
Unfold Reaches₁ and step for configuration ⟨q, [], Z :: α⟩. PDA.step gives:
  { r₂ | ∃ p β, (p,β) ∈ M.toPDA.transition_fun' q Z ∧ r₂ = ⟨p, [], β ++ α⟩ }

Since M.toPDA.transition_fun' q Z = match M.epsilon_transition q Z with some p => {p} | none => ∅
and ht : M.epsilon_transition q Z = some (q', β), we have M.toPDA.transition_fun' q Z = {(q', β)}.

So c must satisfy c = ⟨q', [], β ++ α⟩ (from the set membership in hc).
-/
lemma dpda_epsilon_step_on_empty_input
    (q : Q) (Z : S) (α : List S) (q' : Q) (β : List S)
    (ht : M.epsilon_transition q Z = some (q', β))
    (c : PDA.conf M.toPDA)
    (hc : @PDA.Reaches₁ Q T S _ _ _ M.toPDA ⟨q, [], Z :: α⟩ c) :
    c = ⟨q', [], β ++ α⟩ := by
  obtain ⟨ p, hp ⟩ := hc;
  obtain ⟨ β, hβ, rfl ⟩ := hp; unfold DPDA.toPDA at hβ; aesop;

/-
PROBLEM
If at step i and step j (i < j ≤ n) of a consecutive ε-computation on empty input,
    the (state, stack-top) pair is the same, then the pair at step (i + k) equals the
    pair at step (j + k) for all k such that j + k ≤ n.
    In particular, the computation cycles with period (j - i).

PROVIDED SOLUTION
Since n > 0, we can split: there exists c such that ReachesIn 1 ⟨q, [], γ⟩ c and ReachesIn (n-1) c ⟨q, [], γ⟩ (using reachesIn_iff_split_first).

From h_eps at i = 0: γ has the form Z :: α and M.epsilon_transition q Z ≠ none. So M.epsilon_transition q Z = some (q₁, β₁) for some q₁, β₁. The unique step from ⟨q, [], Z :: α⟩ goes to ⟨q₁, [], β₁ ++ α⟩ (by dpda_epsilon_step_on_empty_input).

So c = ⟨q₁, [], β₁ ++ α⟩.

Now, the computation reaches ⟨q, [], γ⟩ from ⟨q, [], γ⟩ in n steps, and from ⟨q, [], γ⟩ one more step gives ⟨q₁, [], β₁ ++ α⟩.

So ReachesIn (n+1) ⟨q, [], γ⟩ ⟨q₁, [], β₁ ++ α⟩, using ReachesIn.step h (the step from ⟨q, [], γ⟩ to c).

Return q'' = q₁, γ'' = β₁ ++ α.
-/
lemma epsilon_chain_periodic
    (q : Q) (γ : List S) (n : ℕ)
    (h : @PDA.ReachesIn Q T S _ _ _ M.toPDA n ⟨q, [], γ⟩ ⟨q, [], γ⟩)
    (h_eps : ∀ (i : ℕ) (qi : Q) (γi : List S),
      i < n →
      @PDA.ReachesIn Q T S _ _ _ M.toPDA i ⟨q, [], γ⟩ ⟨qi, [], γi⟩ →
      ∃ (Z : S) (αi : List S), γi = Z :: αi ∧ M.epsilon_transition qi Z ≠ none)
    (hn : 0 < n) :
    -- The computation can continue beyond step n (it cycles)
    ∃ (q'' : Q) (γ'' : List S),
      @PDA.ReachesIn Q T S _ _ _ M.toPDA (n + 1) ⟨q, [], γ⟩ ⟨q'', [], γ''⟩ := by
  contrapose! h_eps;
  use 0;
  refine' ⟨ q, γ, hn, _, _ ⟩ <;> norm_num [ ReachesIn.refl ];
  intro Z αi hγ; contrapose! h_eps; simp_all +decide [ ReachesIn.step ] ;
  obtain ⟨q₁, β₁, hq₁⟩ : ∃ q₁ β₁, M.epsilon_transition q Z = some (q₁, β₁) := by
    cases h : M.epsilon_transition q Z <;> tauto
  generalize_proofs at *; (
  have h_step : @PDA.Reaches₁ Q T S _ _ _ M.toPDA ⟨q, [], Z :: αi⟩ ⟨q₁, [], β₁ ++ αi⟩ := by
    have h_step_def : @PDA.step Q T S _ _ _ M.toPDA ⟨q, [], Z :: αi⟩ = {r₂ : PDA.conf M.toPDA | ∃ p β, (p, β) ∈ M.toPDA.transition_fun' q Z ∧ r₂ = ⟨p, [], β ++ αi⟩} := by
      grind
    exact h_step_def.symm.subset ⟨ q₁, β₁, by unfold DPDA.toPDA; aesop ⟩
  generalize_proofs at *; (
  exact ⟨ q₁, β₁ ++ αi, ReachesIn.step h h_step ⟩))

/-- **Pigeonhole bound**: consecutive ε-transitions are bounded by epsilonBound.

    **WARNING**: This lemma is FALSE as stated. The bound `|Q| × |S|` is insufficient
    when ε-transitions can push stack symbols (increasing stack height). A counterexample:
    with Q = {q₀}, S = {Z}, ε(q₀, Z) = (q₀, [Z, Z]), we have epsilonBound = 1 but can
    take arbitrarily many ε-steps. A correct bound would need to account for stack
    growth patterns and is generally exponential in |Q| × |S|.

    The `elimEpsilonLoops` construction should be revised to use a correct bound
    or a different loop-detection mechanism. -/
lemma epsilon_sequence_bounded
    (q q' : Q) (γ γ' : List S)
    (n : ℕ)
    (h : @PDA.ReachesIn Q T S _ _ _ M.toPDA n ⟨q, [], γ⟩ ⟨q', [], γ'⟩)
    (h_all_eps : ∀ (i : ℕ) (qi : Q) (γi : List S),
      i < n →
      @PDA.ReachesIn Q T S _ _ _ M.toPDA i ⟨q, [], γ⟩ ⟨qi, [], γi⟩ →
      ∃ (Z : S) (αi : List S), γi = Z :: αi ∧ M.epsilon_transition qi Z ≠ none) :
    n ≤ epsilonBound (Q := Q) (S := S) := by
  sorry

-- ============================================================================
-- Part 3: Full simulation
-- ============================================================================

/-- The simulation: any finite computation of M can be simulated by the augmented DPDA. -/
lemma elimEpsilonLoops_simulates
    (q q' : Q) (w : List T) (γ γ' : List S)
    (h : @PDA.Reaches Q T S _ _ _ M.toPDA ⟨q, w, γ⟩ ⟨q', [], γ'⟩) :
    ∃ (k k' : Fin (epsilonBound (Q := Q) (S := S) + 1)),
    @PDA.Reaches _ T S _ _ _
      (elimEpsilonLoops M).toPDA
      ⟨(q, k), w, γ⟩ ⟨(q', k'), [], γ'⟩ := by
  sorry

-- ============================================================================
-- Part 4: Language equivalence
-- ============================================================================

/-- The ε-loop-free DPDA accepts the same language as the original. -/
theorem elimEpsilonLoops_language_eq :
    (elimEpsilonLoops M).acceptsByFinalState = M.acceptsByFinalState := by
  sorry

end ElimEpsilonLoops

end DPDA