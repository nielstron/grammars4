/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Grammars.Automata.DetPushdown.Basics.DPDA

/-! # Determinism Properties of DPDAs

This file establishes fundamental determinism properties of DPDAs:
- From any configuration, at most one step is possible.
- The computation path is linear (no branching).
- If two configurations are both reachable from the same start, one is reachable from the other.

These properties are crucial for proving that DPDAs can decide every input.
-/

namespace DPDA

open PDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]
variable (M : DPDA Q T S)

/-
PROBLEM
From any DPDA configuration, at most one next configuration is reachable in one step.
    This is the core determinism property.

PROVIDED SOLUTION
The DPDA has deterministic transitions: `M.transition` and `M.epsilon_transition` return `Option` values (at most one result). The `toPDA` embedding converts `some p` to `{p}` and `none` to `∅`. The `no_mixed` condition ensures ε and input-reading transitions don't coexist.

Case split on the configuration `c`:
- If stack is empty (`c = ⟨q, w, []⟩`): `PDA.step` returns `∅`, so no `c₁, c₂` can be in it — contradiction.
- If stack is `Z :: α` and input is `[]`: only ε-transitions apply. Since `M.epsilon_transition q Z` returns at most one value, if both `c₁` and `c₂` are in step, they must be the same.
- If stack is `Z :: α` and input is `a :: w`: `PDA.step` is a union of input-reading and ε-transition results.
  - If `M.epsilon_transition q Z = some _`, then by `no_mixed`, `M.transition q a Z = none`, so only the ε-transition applies (singleton or empty), giving at most one result.
  - If `M.epsilon_transition q Z = none`, then ε-transitions give `∅`, and `M.transition q a Z` gives at most one result.

In all cases `c₁ = c₂`.
-/
lemma step_deterministic (c c₁ c₂ : PDA.conf M.toPDA)
    (h₁ : PDA.Reaches₁ c c₁) (h₂ : PDA.Reaches₁ c c₂) : c₁ = c₂ := by
  cases c ; cases c₁ ; cases c₂ ; simp_all +decide [ Reaches₁ ];
  unfold PDA.step at h₁ h₂;
  rename_i q w α q' w' α' q'' w'' α'';
  rcases w with ( _ | ⟨ a, w ⟩ ) <;> rcases α with ( _ | ⟨ Z, α ⟩ ) <;> simp_all +decide [ DPDA.toPDA ];
  · cases h : M.epsilon_transition q Z <;> aesop;
  · cases h : M.transition q a Z <;> cases h' : M.epsilon_transition q Z <;> simp_all +decide [ Set.mem_singleton_iff ];
    · grind;
    · grind;
    · have := M.no_mixed q Z ; aesop

/-
PROBLEM
The computation of a DPDA is linear: if both c₁ and c₂ are reachable from c,
    then one is reachable from the other.

PROVIDED SOLUTION
By induction on the derivation of `h₁ : Reaches c c₁`. Use `reaches_iff_reachesIn` to convert to `ReachesIn n`.

Induct on n (the number of steps from c to c₁):
- Base case (n = 0): c₁ = c, so `Reaches c₂ c₁` follows from `h₂` (right disjunct).
- Inductive case: c reaches c₁ in n+1 steps, so there exists c' such that c reaches c' in 1 step and c' reaches c₁ in n steps.
  - Similarly, if c reaches c₂, either c₂ = c (so c reaches c₂ trivially), or c reaches some c₂' in 1 step and c₂' reaches c₂.
  - By `step_deterministic`, c' = c₂' (since both are reached from c in 1 step).
  - Apply the inductive hypothesis to c' reaching both c₁ and c₂.

Actually simpler: induct on `Relation.ReflTransGen`. Base: c = c₁, trivially Reaches c₁ c₂ (right). Step: c → c' →* c₁, and c →* c₂. If c = c₂, done (left). Otherwise c₂ is reached via some c'' in one step from c. By step_deterministic, c' = c''. Apply IH.
-/
lemma reaches_linear (c c₁ c₂ : PDA.conf M.toPDA)
    (h₁ : @PDA.Reaches Q T S _ _ _ M.toPDA c c₁)
    (h₂ : @PDA.Reaches Q T S _ _ _ M.toPDA c c₂) :
    @PDA.Reaches Q T S _ _ _ M.toPDA c₁ c₂ ∨
    @PDA.Reaches Q T S _ _ _ M.toPDA c₂ c₁ := by
  induction' h₁ with c₁ c₂ h₁ h₂ ih generalizing c₂;
  · exact Or.inl h₂;
  · contrapose! ih;
    use c₂;
    -- By the step_deterministic lemma, if there's a path from c₁ to c₂, then they must be the same configuration.
    have h_step_det : ∀ c₁ c₂ : M.toPDA.conf, Reaches₁ c₁ c₂ → ∀ c₃, Reaches₁ c₁ c₃ → c₂ = c₃ := by
      grind +suggestions;
    exact ⟨ h₂, fun h₃ => ih.1 <| by
      obtain ⟨c₃, hc₃⟩ : ∃ c₃, Reaches₁ c₁ c₃ ∧ Reaches c₃ c₂ := by
        have h_step_det : ∀ c₁ c₂ : M.toPDA.conf, Reaches c₁ c₂ → c₁ = c₂ ∨ ∃ c₃, Reaches₁ c₁ c₃ ∧ Reaches c₃ c₂ := by
          intros c₁ c₂ h_reaches
          induction' h_reaches with c₁ c₂ h_reaches ih;
          · exact Or.inl rfl;
          · exact Or.inr <| by rcases ‹_› with ( rfl | ⟨ c₃, hc₃₁, hc₃₂ ⟩ ) <;> [ exact ⟨ c₂, ih, by tauto ⟩ ; exact ⟨ c₃, hc₃₁, by exact Relation.ReflTransGen.trans hc₃₂ <| Relation.ReflTransGen.single ih ⟩ ] ;
        exact h_step_det _ _ h₃ |> Or.resolve_left <| by rintro rfl; tauto;
      exact h_step_det _ _ ‹_› _ hc₃.1 ▸ hc₃.2, fun h₃ => ih.2 <| by
      exact h₃.tail ‹_› ⟩

/-- Consistency of acceptance: if two final configurations (with empty input) are reachable
    from the same starting configuration, one is reachable from the other. -/
lemma reaches_consistent (q₁ q₂ : Q) (w : List T) (γ γ₁ γ₂ : List S)
    (h₁ : @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨M.initial_state, w, γ⟩ ⟨q₁, [], γ₁⟩)
    (h₂ : @PDA.Reaches Q T S _ _ _ M.toPDA
      ⟨M.initial_state, w, γ⟩ ⟨q₂, [], γ₂⟩) :
    @PDA.Reaches Q T S _ _ _ M.toPDA ⟨q₁, [], γ₁⟩ ⟨q₂, [], γ₂⟩ ∨
    @PDA.Reaches Q T S _ _ _ M.toPDA ⟨q₂, [], γ₂⟩ ⟨q₁, [], γ₁⟩ := by
  exact reaches_linear M ⟨M.initial_state, w, γ⟩ ⟨q₁, [], γ₁⟩ ⟨q₂, [], γ₂⟩ h₁ h₂

end DPDA