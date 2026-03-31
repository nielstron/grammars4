/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Grammars.Automata.DetPushdown.Basics.DPDA
import Grammars.Automata.DetPushdown.Basics.Determinism

/-! # Making DPDAs Total

This file constructs a total DPDA from a given DPDA: one that decides every input word.

## Strategy

Given a DPDA `M` (assumed to have no infinite ε-loops, e.g. after epsilon elimination),
we construct a new DPDA `M'` that:
1. Adds a **fresh initial state** that ε-transitions to push the original start symbol
   above a bottom-of-stack marker.
2. Adds a **sink state** that reads all remaining input without accepting.
3. The **bottom-of-stack marker** (`none : Option S`) ensures the stack never becomes
   empty (since PDA transitions require a non-empty stack).
4. Whenever the original DPDA would get stuck (no transition defined), redirects to
   the sink state.

## State encoding

We use `Option (Option Q)` for the state type:
- `some (some q)` — original state `q` of the input DPDA
- `some none`     — fresh initial state (performs one ε-transition to set up the stack)
- `none`          — sink (dead) state

## Stack encoding

We use `Option S` for the stack type:
- `some Z` — original stack symbol `Z`
- `none`   — bottom-of-stack marker (always at the very bottom)

## Main definitions

- `DPDA.makeTotal` — the total DPDA construction

## Main results

- `makeTotal_language_eq` — the total DPDA accepts the same language
- `makeTotal_decidesEveryInput` — the total DPDA decides every input
  (under the assumption that the original DPDA has no infinite ε-loops)
-/

namespace DPDA

open PDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

section MakeTotal

variable (M : DPDA Q T S)

/-- The transition function for `makeTotal`. Factored out for readability. -/
private noncomputable def makeTotalTransition :
    Option (Option Q) → T → Option S → Option (Option (Option Q) × List (Option S)) :=
  fun oq a oZ =>
    match oq with
    | some none => none
    | none => some (none, [oZ])
    | some (some q) =>
      match oZ with
      | none => some (none, [none])
      | some Z =>
        match M.epsilon_transition q Z with
        | some _ => none
        | none =>
          match M.transition q a Z with
          | some (q', β) => some (some (some q'), β.map some)
          | none => some (none, [some Z])

/-- The ε-transition function for `makeTotal`. Factored out for readability. -/
private noncomputable def makeTotalEpsilon :
    Option (Option Q) → Option S → Option (Option (Option Q) × List (Option S)) :=
  fun oq oZ =>
    match oq with
    | some none =>
      match oZ with
      | none => some (some (some M.initial_state), [some M.start_symbol, none])
      | some _ => none
    | none => none
    | some (some q) =>
      match oZ with
      | some Z =>
        match M.epsilon_transition q Z with
        | some (q', β) => some (some (some q'), β.map some)
        | none => none
      | none => none

/-- Construct a total DPDA from the given DPDA. -/
noncomputable def makeTotal : DPDA (Option (Option Q)) T (Option S) where
  initial_state := some none
  start_symbol := none
  final_states := { q | ∃ q' ∈ M.final_states, q = some (some q') }
  transition := makeTotalTransition M
  epsilon_transition := makeTotalEpsilon M
  no_mixed := by
    intro oq oZ heps a
    rcases oq with _ | (_ | q) <;> rcases oZ with _ | Z <;>
      simp only [ne_eq, makeTotalEpsilon, makeTotalTransition] at heps ⊢ <;>
      first | exact absurd rfl heps | rfl | exact (heps trivial).elim | skip
    cases h : M.epsilon_transition q Z with
    | none => simp [h] at heps
    | some p => simp [h]

-- ============================================================================
-- Basic helper lemmas
-- ============================================================================

lemma makeTotal_sink_not_final : (none : Option (Option Q)) ∉ (makeTotal M).final_states := by
  simp [makeTotal]

lemma makeTotal_init_not_final :
    (some none : Option (Option Q)) ∉ (makeTotal M).final_states := by
  simp [makeTotal]

lemma makeTotal_sink_reads_all (w : List T) (γ : List (Option S)) (hγ : γ ≠ []) :
    @PDA.Reaches (Option (Option Q)) T (Option S) _ _ _
      (makeTotal M).toPDA ⟨none, w, γ⟩ ⟨none, [], γ⟩ := by
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | cons a w' ih =>
    obtain ⟨Z, rest, rfl⟩ := List.exists_cons_of_ne_nil hγ
    exact (Relation.ReflTransGen.single (by
      unfold Reaches₁ step; left
      exact ⟨none, [Z], by unfold DPDA.toPDA makeTotal makeTotalTransition; simp, by simp⟩)).trans ih

lemma makeTotal_init_epsilon_step (w : List T) :
    @PDA.Reaches₁ (Option (Option Q)) T (Option S) _ _ _
      (makeTotal M).toPDA
      ⟨some none, w, [none]⟩
      ⟨some (some M.initial_state), w, [some M.start_symbol, none]⟩ := by
  unfold Reaches₁; simp +decide [PDA.step]
  cases w <;> simp_all +decide [DPDA.makeTotal]
  · unfold DPDA.toPDA; aesop
  · unfold DPDA.toPDA; unfold DPDA.makeTotalEpsilon; aesop

lemma makeTotal_lift_input_step
    (q q' : Q) (a : T) (w : List T) (Z : S) (α β : List S)
    (ht : M.transition q a Z = some (q', β))
    (heps : M.epsilon_transition q Z = none) :
    @PDA.Reaches₁ (Option (Option Q)) T (Option S) _ _ _
      (makeTotal M).toPDA
      ⟨some (some q), a :: w, (some Z) :: (α.map some ++ [none])⟩
      ⟨some (some q'), w, β.map some ++ (α.map some ++ [none])⟩ := by
  convert Set.mem_union_left _ _ using 1
  simp [DPDA.makeTotal, DPDA.toPDA]
  unfold DPDA.makeTotalTransition; aesop

lemma makeTotal_lift_epsilon_step
    (q q' : Q) (w : List T) (Z : S) (α β : List S)
    (ht : M.epsilon_transition q Z = some (q', β)) :
    @PDA.Reaches₁ (Option (Option Q)) T (Option S) _ _ _
      (makeTotal M).toPDA
      ⟨some (some q), w, (some Z) :: (α.map some ++ [none])⟩
      ⟨some (some q'), w, β.map some ++ (α.map some ++ [none])⟩ := by
  unfold Reaches₁ step DPDA.toPDA DPDA.makeTotal
  rcases w with (_ | ⟨a, w⟩) <;> simp +decide [*, DPDA.makeTotalEpsilon]

-- ============================================================================
-- Simulation (M → makeTotal)
-- ============================================================================

lemma makeTotal_simulates
    (q q' : Q) (w : List T) (γ γ' : List S)
    (h : @PDA.Reaches Q T S _ _ _ M.toPDA ⟨q, w, γ⟩ ⟨q', [], γ'⟩) :
    @PDA.Reaches (Option (Option Q)) T (Option S) _ _ _
      (makeTotal M).toPDA
      ⟨some (some q), w, γ.map some ++ [none]⟩
      ⟨some (some q'), [], γ'.map some ++ [none]⟩ := by
  have h_lift : ∀ r₁ r₂ : PDA.conf M.toPDA, M.toPDA.Reaches r₁ r₂ →
      (makeTotal M).toPDA.Reaches
        ⟨some (some r₁.state), r₁.input, r₁.stack.map some ++ [none]⟩
        ⟨some (some r₂.state), r₂.input, r₂.stack.map some ++ [none]⟩ := by
    intro r₁ r₂ h_reaches
    induction h_reaches with
    | refl => exact Reaches.refl _
    | @tail c₁ c₂ _ hstep ih =>
      refine' ih.trans _
      rcases c₁ with ⟨q₁, w₁, γ₁⟩; rcases c₂ with ⟨q₂, w₂, γ₂⟩
      simp only at hstep ⊢
      rcases w₁ with (_ | ⟨a, w₁⟩) <;> rcases γ₁ with (_ | ⟨Z, γ₁⟩) <;>
        simp +decide [Reaches₁, step] at hstep
      · obtain ⟨β, hβ₁, rfl, rfl⟩ := hstep
        simp +decide [DPDA.toPDA] at hβ₁
        cases h : M.epsilon_transition q₁ Z <;> simp_all +decide [Set.mem_singleton_iff]
        exact .single (makeTotal_lift_epsilon_step _ _ _ _ _ _ _ (by aesop))
      · rcases hstep with (⟨β, hβ, rfl, rfl⟩ | ⟨β, hβ, rfl, rfl⟩) <;>
          simp +decide [DPDA.toPDA] at hβ
        · rcases h : M.transition q₁ a Z with (_ | ⟨q₂, β⟩) <;> simp_all +decide [Reaches₁]
          exact .single (makeTotal_lift_input_step _ _ _ _ _ _ _ _
            (by exact h) (by
              by_contra h'; push_neg at h'
              have := M.no_mixed q₁ Z h' a
              simp [this] at h))
        · cases h : M.epsilon_transition q₁ Z <;> simp_all +decide [Set.mem_singleton_iff]
          exact .single (makeTotal_lift_epsilon_step _ _ _ _ _ _ _ (by aesop))
  exact h_lift _ _ h

/-
PROBLEM
============================================================================
Projection helpers (makeTotal → M)
============================================================================

From state `some (some q)`, a single step of makeTotal produces state
    `some (some q')` or `none` — never `some none` (the init state).

PROVIDED SOLUTION
Case split on the step. From ⟨some (some q), w, γ⟩, unfold step and toPDA. The transitions from state some (some q) are:
- transition (some (some q)) a oZ: produces some (some q') or none, never some none
- epsilon (some (some q)) oZ: produces some (some q') or none, never some none

So c.state is either some (some q') for some q', or none.

Concretely: unfold Reaches₁ and step. Case split on w and γ.
- γ = []: step returns ∅, contradiction with h.
- γ = oZ :: rest, w = []: step gives ε-transitions only. From (some (some q), oZ): if oZ = none, epsilon returns none (no step, contradiction). If oZ = some Z, epsilon checks M.epsilon_transition q Z. If some (q', β), produces some (some q'). If none, no step. Either way, c.state = some (some q') for some q'.
- γ = oZ :: rest, w = a :: w': step gives union. Input transitions from (some (some q), a, oZ): if oZ = none → (none, [none]). If oZ = some Z → cases on M.epsilon_transition q Z: if some _ → none (no input); if none → cases M.transition q a Z: some (q', β) → (some (some q'), ..); none → (none, ..). ε transitions similar to above.

In ALL cases, the resulting state is some (some q') or none. Never some none, because makeTotalTransition at some (some q) never returns some none, and makeTotalEpsilon at some (some q) never returns some none.
-/
lemma makeTotal_step_from_original
    (q : Q) (w : List T) (γ : List (Option S))
    (c : PDA.conf (makeTotal M).toPDA)
    (h : @PDA.Reaches₁ (Option (Option Q)) T (Option S) _ _ _
      (makeTotal M).toPDA ⟨some (some q), w, γ⟩ c) :
    (∃ q' : Q, c.state = some (some q')) ∨ c.state = none := by
  unfold Reaches₁ at h;
  unfold PDA.step at h; rcases w with ( _ | ⟨ a, w ⟩ ) <;> rcases γ with ( _ | ⟨ Z, γ ⟩ ) <;> simp_all +decide ;
  · unfold DPDA.toPDA at h;
    rcases h with ⟨ p, β, hp, rfl ⟩ ; rcases Z with ( _ | Z ) <;> simp +decide [ DPDA.makeTotal ] at hp ⊢;
    · unfold DPDA.makeTotalEpsilon at hp; aesop;
    · unfold DPDA.makeTotalEpsilon at hp;
      cases h : M.epsilon_transition q Z <;> aesop;
  · rcases Z with ( _ | Z ) <;> simp_all +decide [ DPDA.makeTotal ];
    · unfold DPDA.toPDA at h; simp_all +decide [ DPDA.makeTotalEpsilon ] ;
      unfold DPDA.makeTotalTransition at h; aesop;
    · rcases h with ( ⟨ p, β, h, rfl ⟩ | ⟨ p, β, h, rfl ⟩ ) <;> simp_all +decide [ DPDA.toPDA ];
      · unfold DPDA.makeTotalTransition at h;
        cases h' : M.epsilon_transition q Z <;> cases h'' : M.transition q a Z <;> aesop;
      · cases h' : M.epsilon_transition q Z <;> simp_all +decide [ DPDA.makeTotalEpsilon ]

/-- Once in the sink state, the state stays `none` forever. -/
lemma makeTotal_sink_stays_sink
    (w : List T) (γ : List (Option S))
    (c : PDA.conf (makeTotal M).toPDA)
    (h : @PDA.Reaches (Option (Option Q)) T (Option S) _ _ _
      (makeTotal M).toPDA ⟨none, w, γ⟩ c) :
    c.state = none := by
  have h_sink : ∀ (c : PDA.conf (makeTotal M).toPDA), c.state = none →
      ∀ (c' : PDA.conf (makeTotal M).toPDA), Reaches₁ c c' → c'.state = none := by
    intro c hc c' hc'
    rcases c with ⟨q, w, γ⟩; rcases c' with ⟨q', w', γ'⟩
    rcases γ with (_ | ⟨Z, α⟩) <;> simp_all +decide [Reaches₁]
    · unfold step at hc'; aesop
    · cases w <;> cases Z <;> cases γ' <;> simp_all +decide [step] <;>
        (try unfold DPDA.toPDA at hc'; simp_all +decide [DPDA.makeTotalEpsilon, DPDA.makeTotalTransition]) <;>
        (try unfold DPDA.makeTotal at hc'; simp_all +decide [DPDA.makeTotalEpsilon, DPDA.makeTotalTransition])
  induction h <;> aesop

/-
PROBLEM
If a step from `some (some q)` with stack `α.map some ++ [none]` produces state
    `some (some q')`, then the new stack has the form `β.map some ++ [none]` and M has
    a corresponding step.

PROVIDED SOLUTION
Case split on α and w.

Case α = []: stack = [none]. The top is none. From (some (some q), w, none :: []):
- Input: transition (some (some q)) a none = some (none, [none]). State = none ≠ some (some q'). The hypothesis says c.state = some (some q'), so this case is impossible.
- ε: epsilon (some (some q)) none = none. No ε-transition.
So if α = [], there's no step that produces some (some q'). Contradiction with h.

Case α = Z :: rest: stack = (some Z) :: (rest.map some ++ [none]).
- ε-transition: epsilon (some (some q)) (some Z) = match M.epsilon_transition q Z. If some (q', β), produces (some (some q'), β.map some). New stack: β.map some ++ (rest.map some ++ [none]) = (β ++ rest).map some ++ [none]. And M has step (q, Z :: rest) → (q', β ++ rest) via ε.
- Input transition (w = a :: w'): transition (some (some q)) a (some Z). If M.epsilon_transition q Z = none and M.transition q a Z = some (q', β): produces (some (some q'), β.map some). Same stack analysis. M has step via input.
- Input transition with M.epsilon_transition q Z ≠ none: returns none (no_mixed). No input step.
- Input transition with M.transition q a Z = none: produces (none, [some Z]). State = none, not some (some q'). Contradiction.
- transition on (some (some q), a, none) = (none, [none]). State = none. Contradiction.

In valid cases: γ' = (β ++ rest).map some ++ [none] and M has the corresponding step. So ∃ β' := β ++ rest works... wait no. Let me reconsider.

Actually, the step replaces the top element Z with β, keeping rest below. In M: Z :: rest → β ++ rest. In makeTotal: (some Z) :: (rest.map some ++ [none]) → β.map some ++ (rest.map some ++ [none]).

So γ' = β.map some ++ (rest.map some ++ [none]) = (β ++ rest).map some ++ [none]. The witness is β' = β ++ rest.

And M.toPDA.Reaches₁ ⟨q, w, Z :: rest⟩ ⟨q', w', β ++ rest⟩. This is exactly what PDA step gives: from Z :: rest, replace Z with β, new stack = β ++ rest.

So the proof: case split on the step, extract β from the transition, use β ++ rest as the witness. Note that α = Z :: rest, so the conclusion ∃ β', γ' = β'.map some ++ [none] ∧ M.Reaches₁ ⟨q, w, Z :: rest⟩ ⟨q', w', β'⟩ is satisfied with β' = β ++ rest.

Wait, actually I need to be more careful. The Reaches₁ in M: ⟨q, w, α⟩ → ⟨q', w', β'⟩. Here α = Z :: rest. The PDA step gives β' as β ++ rest (where β is the replacement list from the transition). So yes, β' = β ++ rest.

Key: unfold step and toPDA, case split on transitions, show state can only be some (some q') from the valid transitions, and extract the witness.
-/
lemma makeTotal_step_preserves_invariant
    (q q' : Q) (w w' : List T) (α : List S) (γ' : List (Option S))
    (h : @PDA.Reaches₁ (Option (Option Q)) T (Option S) _ _ _
      (makeTotal M).toPDA
      ⟨some (some q), w, α.map some ++ [none]⟩
      ⟨some (some q'), w', γ'⟩) :
    ∃ β : List S, γ' = β.map some ++ [none] ∧
      @PDA.Reaches₁ Q T S _ _ _ M.toPDA ⟨q, w, α⟩ ⟨q', w', β⟩ := by
  rcases w with ( _ | ⟨ a, w ⟩ ) <;> rcases α with ( _ | ⟨ Z, α ⟩ ) <;> simp_all +decide [ Reaches₁ ];
  · cases h ; tauto;
  · unfold step at h; simp_all +decide [ List.map ] ;
    obtain ⟨ β, hβ₁, rfl, rfl ⟩ := h;
    unfold DPDA.toPDA at hβ₁; simp_all +decide [ DPDA.makeTotal ] ;
    rcases h : M.epsilon_transition q Z with ( _ | ⟨ q', β ⟩ ) <;> simp_all +decide [ DPDA.makeTotalEpsilon ];
    use β ++ α; simp_all +decide [ step ] ;
    unfold DPDA.toPDA; aesop;
  · cases h' : γ' <;> simp_all +decide [ step ];
    · unfold DPDA.toPDA at * ; simp_all +decide [ DPDA.makeTotal ];
      unfold DPDA.makeTotalTransition DPDA.makeTotalEpsilon at h ; aesop;
    · cases h <;> simp_all +decide [ DPDA.makeTotal, DPDA.toPDA ];
      · unfold DPDA.makeTotalTransition at * ; aesop;
      · unfold DPDA.makeTotalEpsilon at * ; aesop;
  · unfold step at h ⊢; simp_all +decide [ DPDA.toPDA ] ;
    unfold DPDA.makeTotal at h;
    unfold DPDA.makeTotalTransition DPDA.makeTotalEpsilon at h; rcases x : M.transition q a Z with ( _ | ⟨ q'', β ⟩ ) <;> rcases y : M.epsilon_transition q Z with ( _ | ⟨ q''', β' ⟩ ) <;> simp_all +decide ;

/-
PROBLEM
Multi-step projection: if makeTotal stays on original states with the stack invariant,
    then M has a corresponding multi-step computation.

PROVIDED SOLUTION
Prove by establishing an invariant via induction on Reaches (ReflTransGen).

Main claim (proved by induction on Reaches): If makeTotal reaches c from ⟨some (some q), w, α.map some ++ [none]⟩, then either:
(a) c.state = none (entered sink), OR
(b) ∃ c' : PDA.conf M.toPDA, M.toPDA.Reaches ⟨q, w, α⟩ c' ∧ c = ⟨some (some c'.state), c'.input, c'.stack.map some ++ [none]⟩

Base case (refl): option (b) with c' = ⟨q, w, α⟩.

Inductive case (tail): Reaches start c₁ and Reaches₁ c₁ c₂.
- If IH gives (a): c₁.state = none. By makeTotal_sink_stays_sink step, c₂.state = none. So option (a) for c₂.
- If IH gives (b): c₁ = ⟨some (some c'.state), c'.input, c'.stack.map some ++ [none]⟩ and M reaches c' from (q, w, α).
  - By makeTotal_step_from_original on c₁ → c₂: c₂.state = some (some q₂) for some q₂, or c₂.state = none.
  - If c₂.state = none: option (a).
  - If c₂.state = some (some q₂): by makeTotal_step_preserves_invariant on c₁ → c₂ (with c₁.state = some (some c'.state) and stack = c'.stack.map some ++ [none]), get ∃ β, c₂.stack = β.map some ++ [none] ∧ M.Reaches₁ c' ⟨q₂, c₂.input, β⟩. So option (b) with c'' = ⟨q₂, c₂.input, β⟩.

After establishing the invariant: apply to h. Since c = ⟨some (some q'), [], α'.map some ++ [none]⟩, option (a) is impossible (c.state = some (some q') ≠ none). So option (b) holds: M reaches c' from (q, w, α) and c' = ⟨q', [], α'⟩ (by matching state, input, and stack). So M.Reaches ⟨q, w, α⟩ ⟨q', [], α'⟩.
-/
lemma makeTotal_projects
    (q q' : Q) (w : List T) (α α' : List S)
    (h : @PDA.Reaches (Option (Option Q)) T (Option S) _ _ _
      (makeTotal M).toPDA
      ⟨some (some q), w, α.map some ++ [none]⟩
      ⟨some (some q'), [], α'.map some ++ [none]⟩) :
    @PDA.Reaches Q T S _ _ _ M.toPDA ⟨q, w, α⟩ ⟨q', [], α'⟩ := by
  have h_inv : ∀ c : PDA.conf (makeTotal M).toPDA, @PDA.Reaches (Option (Option Q)) T (Option S) _ _ _ (makeTotal M).toPDA ⟨some (some q), w, α.map some ++ [none]⟩ c → (∃ c' : PDA.conf M.toPDA, M.toPDA.Reaches ⟨q, w, α⟩ c' ∧ c = ⟨some (some c'.state), c'.input, c'.stack.map some ++ [none]⟩) ∨ c.state = none := by
    intro c hc
    induction' hc with c₁ c₂ hc₁ hc₂ ih
    generalize_proofs at *; (
    exact Or.inl ⟨ ⟨ q, w, α ⟩, by rfl, rfl ⟩);
    rcases ih with ( ⟨ c', hc', rfl ⟩ | hc' );
    · rcases makeTotal_step_from_original M c'.state c'.input ( c'.stack.map some ++ [ none ] ) c₂ hc₂ with ( ⟨ q'', hq'' ⟩ | hq'' ) <;> simp_all +decide [ Reaches₁ ];
      rcases makeTotal_step_preserves_invariant M c'.state q'' c'.input c₂.input c'.stack c₂.stack (by
      exact hq''.symm ▸ hc₂) with ⟨ β, hβ₁, hβ₂ ⟩
      generalize_proofs at *;
      exact ⟨ ⟨ q'', c₂.input, β ⟩, hc'.trans ( Relation.ReflTransGen.single hβ₂ ), by cases c₂; aesop ⟩;
    · have h_sink : ∀ c : PDA.conf (makeTotal M).toPDA, c.state = none → ∀ c' : PDA.conf (makeTotal M).toPDA, Reaches₁ c c' → c'.state = none := by
        intros c hc c' hc'; exact (by
        have := @makeTotal_sink_stays_sink Q T S _ _ _ M c.input c.stack c';
        exact this ( Relation.ReflTransGen.single <| by cases c; aesop ));
      exact Or.inr ( h_sink _ hc' _ hc₂ );
  cases h_inv _ h <;> simp_all +decide [ PDA.Reaches ];
  rename_i h; obtain ⟨ c', hc₁, rfl, hc₂, hc₃ ⟩ := h; simp_all +decide [ List.map_inj_right ] ;
  cases c' ; aesop

/-
PROBLEM
============================================================================
Language equivalence
============================================================================

If makeTotal reaches a config with state `some (some q')` from a config with
    stack invariant, then the final stack also has the invariant form.

PROVIDED SOLUTION
Use the same invariant as in makeTotal_projects. In fact, the proof of makeTotal_projects already establishes:

∀ c, Reaches ⟨some (some q), w, α.map some ++ [none]⟩ c →
  (∃ c' : M.toPDA.conf, M.toPDA.Reaches ⟨q, w, α⟩ c' ∧ c = ⟨some (some c'.state), c'.input, c'.stack.map some ++ [none]⟩) ∨ c.state = none

Apply this invariant to c = ⟨some (some q'), [], γ'⟩. Since c.state = some (some q') ≠ none, the first disjunct holds: ∃ c', c = ⟨some (some c'.state), c'.input, c'.stack.map some ++ [none]⟩. So γ' = c'.stack.map some ++ [none]. Use α' = c'.stack.

So the proof just needs to establish this invariant by induction on Reaches, then instantiate it.

The induction is exactly the same as in makeTotal_projects. Rather than reproving it, note that the invariant can be extracted from the proof of makeTotal_projects, or proved with the same technique.

Key step in the inductive case: when state stays some (some q_i) (by makeTotal_step_from_original), apply makeTotal_step_preserves_invariant to get the stack form. When state becomes none (sink), track that the state stays none.

Actually, simplest approach: just directly prove this as a corollary of the invariant. Induct on Reaches (Relation.ReflTransGen):
- refl: α' = α
- tail: from c₁ →* c₂ →₁ ⟨some (some q'), [], γ'⟩.
  - By IH (or separate case): c₁ satisfies invariant OR c₁.state = none.
  - If c₁.state = none: by sink step, c₂.state = none = some (some q'). Contradiction.
  - If c₁ has stack β.map some ++ [none] and state some (some q₁): apply makeTotal_step_preserves_invariant to the step c₁ →₁ c₂ to get ∃ β', c₂.stack = β'.map some ++ [none]. So α' = β'.
-/
lemma makeTotal_stack_form
    (q q' : Q) (w : List T) (α : List S) (γ' : List (Option S))
    (h : @PDA.Reaches (Option (Option Q)) T (Option S) _ _ _
      (makeTotal M).toPDA
      ⟨some (some q), w, α.map some ++ [none]⟩
      ⟨some (some q'), [], γ'⟩) :
    ∃ α' : List S, γ' = α'.map some ++ [none] := by
  contrapose! h;
  intro h';
  have h_invariant : ∀ c, @PDA.Reaches (Option (Option Q)) T (Option S) _ _ _ (makeTotal M).toPDA ⟨some (some q), w, α.map some ++ [none]⟩ c → (∃ c' : M.toPDA.conf, @PDA.Reaches Q T S _ _ _ M.toPDA ⟨q, w, α⟩ c' ∧ c = ⟨some (some c'.state), c'.input, c'.stack.map some ++ [none]⟩) ∨ c.state = none := by
    intro c hc
    induction' hc with c₁ c₂ hc₁ hc₂ ih;
    · exact Or.inl ⟨ ⟨ q, w, α ⟩, by rfl, rfl ⟩;
    · rcases ih with ( ⟨ c', hc', rfl ⟩ | hc' );
      · rcases makeTotal_step_from_original M c'.state c'.input ( List.map some c'.stack ++ [ none ] ) c₂ hc₂ with ( ⟨ q', hq' ⟩ | hq' ) <;> simp_all +decide [ Reaches₁ ];
        obtain ⟨ β, hβ₁, hβ₂ ⟩ := makeTotal_step_preserves_invariant M c'.state q' c'.input c₂.input c'.stack c₂.stack ( by
          cases c₂ ; aesop );
        exact ⟨ ⟨ q', c₂.input, β ⟩, hc'.trans ( Relation.ReflTransGen.single hβ₂ ), by cases c₂; aesop ⟩;
      · have h_contradiction : c₂.state = none := by
          convert makeTotal_sink_stays_sink M c₁.input c₁.stack c₂ _;
          exact Relation.ReflTransGen.single ( by cases c₁; aesop );
        exact Or.inr h_contradiction;
  grind

/-
PROBLEM
The total DPDA accepts the same language as the original.

PROVIDED SOLUTION
ext w; constructor.

(⊇ direction - M accepts w implies makeTotal accepts w):
Obtain q' ∈ M.final_states and γ with M.toPDA.Reaches from initial to (q', [], γ).
By makeTotal_simulates: makeTotal reaches (some (some q'), [], γ.map some ++ [none]) from (some (some M.initial_state), w, [some M.start_symbol, none]).
Prepend init ε-step: makeTotal reaches from ⟨some none, w, [none]⟩ to ⟨some (some q'), [], γ.map some ++ [none]⟩.
Since q' ∈ M.final_states, some (some q') ∈ makeTotal.final_states.
Done: use some (some q') and γ.map some ++ [none] as witnesses.

(⊆ direction - makeTotal accepts w implies M accepts w):
Obtain oq ∈ makeTotal.final_states and γ' with makeTotal.toPDA.Reaches from initial.
oq = some (some q') for some q' ∈ M.final_states (from the definition of final_states).

Now: the computation from ⟨some none, w, [none]⟩ to ⟨some (some q'), [], γ'⟩.
The first step from ⟨some none, w, [none]⟩ must be the init ε-step (by step_deterministic of makeTotal, since makeTotal_init_epsilon_step gives a step, and by step analysis there's only one possible step from this config).

Actually, we don't need step_deterministic. We can just use Relation.ReflTransGen inversion: since some none ≠ some (some q'), the relation is not refl. So there exists a first step. The first step goes to c₁. By step analysis of ⟨some none, w, [none]⟩, the only possible step is to ⟨some (some M.initial_state), w, [some M.start_symbol, none]⟩. By step_deterministic, c₁ = this config. Then the rest is Reaches from ⟨some (some M.initial_state), w, [some M.start_symbol, none]⟩ to ⟨some (some q'), [], γ'⟩.

By makeTotal_stack_form: ∃ α', γ' = α'.map some ++ [none].
By makeTotal_projects: M.toPDA.Reaches ⟨M.initial_state, w, [M.start_symbol]⟩ ⟨q', [], α'⟩.
Done: use q' and α' as witnesses.

Key lemmas: makeTotal_simulates, makeTotal_init_epsilon_step, makeTotal_stack_form, makeTotal_projects, step_deterministic (for the init step), reaches_linear.
-/
theorem makeTotal_language_eq :
    (makeTotal M).acceptsByFinalState = M.acceptsByFinalState := by
  apply Set.ext
  intro w
  constructor
  intro hw
  obtain ⟨q, hq, γ, hγ⟩ := hw
  generalize_proofs at *; (
  cases' q with q q <;> simp_all +decide [ DPDA.makeTotal ];
  · cases hq ; aesop;
  · cases' hq with q' hq' hq''; simp_all +decide [ PDA.acceptsByFinalState ] ;
    obtain ⟨c₁, hc₁⟩ : ∃ c₁, @PDA.Reaches₁ (Option (Option Q)) T (Option S) _ _ _ (makeTotal M).toPDA ⟨some none, w, [none]⟩ c₁ ∧ @PDA.Reaches (Option (Option Q)) T (Option S) _ _ _ (makeTotal M).toPDA c₁ ⟨some (some q'), [], γ⟩ := by
      have h_split : ∀ {c₁ c₂ : PDA.conf (makeTotal M).toPDA}, @PDA.Reaches (Option (Option Q)) T (Option S) _ _ _ (makeTotal M).toPDA c₁ c₂ → c₁ ≠ c₂ → ∃ c₃, @PDA.Reaches₁ (Option (Option Q)) T (Option S) _ _ _ (makeTotal M).toPDA c₁ c₃ ∧ @PDA.Reaches (Option (Option Q)) T (Option S) _ _ _ (makeTotal M).toPDA c₃ c₂ := by
        intros c₁ c₂ h₁ h₂; exact (by
        have := Relation.ReflTransGen.cases_head h₁; aesop;);
      generalize_proofs at *; (
      apply h_split hγ; simp [hq'];
      exact fun h => absurd h ( by simp +decide [ DPDA.toPDA ] ));
    have h_step : c₁ = ⟨some (some M.initial_state), w, [some M.start_symbol, none]⟩ := by
      apply DPDA.step_deterministic; exact hc₁.left; exact makeTotal_init_epsilon_step M w;
    generalize_proofs at *; (
    have := makeTotal_stack_form M M.initial_state q' w [M.start_symbol] γ (by
    aesop)
    generalize_proofs at *; (
    obtain ⟨ α', rfl ⟩ := this; exact ⟨ q', hq'.1, α', by simpa [ h_step ] using makeTotal_projects M M.initial_state q' w [ M.start_symbol ] α' ( by simpa [ h_step ] using hc₁.2 ) ⟩ ;)));
  rintro ⟨ q, hq, γ, h ⟩;
  use some (some q);
  refine' ⟨ _, _ ⟩
  all_goals generalize_proofs at *;
  · exact ⟨ q, hq, rfl ⟩;
  · use γ.map some ++ [none];
    have := makeTotal_simulates M M.initial_state q w [ M.toPDA.start_symbol ] γ h;
    exact Relation.ReflTransGen.trans ( Relation.ReflTransGen.single ( makeTotal_init_epsilon_step M w ) ) this

-- ============================================================================
-- Totality (decides every input)
-- ============================================================================

/-- A DPDA has **no infinite ε-loops** if from every configuration (q, [], γ)
    with non-empty stack, consecutive ε-chains have a finite bound. -/
def NoInfiniteEpsilonLoops (M : DPDA Q T S) : Prop :=
  ∀ (q : Q) (γ : List S), γ ≠ [] →
    ∃ (N : ℕ), ∀ (n : ℕ) (q' : Q) (γ' : List S),
      @PDA.ReachesIn Q T S _ _ _ M.toPDA n ⟨q, [], γ⟩ ⟨q', [], γ'⟩ →
      (∀ (i : ℕ) (qi : Q) (γi : List S),
        i < n →
        @PDA.ReachesIn Q T S _ _ _ M.toPDA i ⟨q, [], γ⟩ ⟨qi, [], γi⟩ →
        ∃ (Z : S) (αi : List S), γi = Z :: αi ∧ M.epsilon_transition qi Z ≠ none) →
      n ≤ N

/-- The total DPDA decides every input. Requires no infinite ε-loops. -/
theorem makeTotal_decidesEveryInput (hM : NoInfiniteEpsilonLoops M) :
    (makeTotal M).DecidesEveryInput := by
  sorry

end MakeTotal

end DPDA