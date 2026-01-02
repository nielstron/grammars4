import Grammars.Classes.ContextFree.Basics.Definition
import Grammars.Classes.ContextFree.Basics.Toolbox
import Grammars.Utilities.ListUtils
import LeanCopilot

open List

variable {T : Type}

-- Helper lemma about n_times and successor (left-associative)
lemma n_times_succ (l : List α) (n : ℕ) : l ^ (n + 1) = l ++ l ^ n := by
  unfold n_times
  rw [List.replicate_succ_eq_singleton_append]
  rfl

-- Helper lemma about n_times and successor (right-associative)
lemma n_times_succ_append (l : List α) (n : ℕ) : l ^ (n + 1) = l ^ n ++ l := by
  unfold n_times
  rw [List.replicate_succ_eq_append_singleton]
  simp [List.flatten, List.reverse_append]

-- Helper lemma: map distributes over n_times
lemma map_n_times {α β : Type*} (f : α → β) (l : List α) (n : ℕ) :
    List.map f (l ^ n) = (List.map f l) ^ n := by
  unfold n_times
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ_eq_singleton_append, List.replicate_succ_eq_singleton_append]
    simp [List.flatten, List.map_append, ih]

-- Auxiliary lemma: iterating the loop gives us u^i ++ [A] ++ v^i
lemma iterate_loop {g : CF_grammar T} {A : g.nt} {u v : List (symbol T g.nt)}
    (h_loop : CF_derives g [symbol.nonterminal A] (u ++ [symbol.nonterminal A] ++ v)) :
    ∀ i : ℕ, CF_derives g [symbol.nonterminal A] (u ^ i ++ [symbol.nonterminal A] ++ v ^ i) :=
by
  intro i
  induction i with
  | zero =>
    -- Base case: i = 0, need [A] → []++[A]++[] = [A]
    unfold n_times
    simp [List.replicate, List.flatten]
    exact CF_deri_self
  | succ i' ih =>
    -- Inductive step: have [A] → u^i'++[A]++v^i', want [A] → u^(i'+1)++[A]++v^(i'+1)
    -- Strategy: [A] → u++[A]++v → u++(u^i'++[A]++v^i')++v = u^(i'+1)++[A]++v^(i'+1)

    -- First apply the loop rule
    have step1 := h_loop

    -- Then expand [A] using the inductive hypothesis
    have step2 : CF_derives g (u ++ [symbol.nonterminal A] ++ v) (u ++ (u ^ i' ++ [symbol.nonterminal A] ++ v ^ i') ++ v) := by
      apply CF_deri_with_prefix_and_postfix u v ih

    -- Chain the derivations
    have combined := CF_deri_of_deri_deri step1 step2

    -- Show the result equals u^(i'+1)++[A]++v^(i'+1)
    have eq : u ++ (u ^ i' ++ [symbol.nonterminal A] ++ v ^ i') ++ v = u ^ (i' + 1) ++ [symbol.nonterminal A] ++ v ^ (i' + 1) := by
      rw [n_times_succ u i', n_times_succ_append v i']
      simp only [List.append_assoc]

    rw [←eq]
    exact combined

-- Key helper lemma: pumping by iterating a derivation loop
-- If A derives u++[A]++v and A derives w, then for any i, we can derive u^i++w++v^i
lemma pump_loop {g : CF_grammar T} {A : g.nt} {u v w : List (symbol T g.nt)}
    (h_loop : CF_derives g [symbol.nonterminal A] (u ++ [symbol.nonterminal A] ++ v))
    (h_base : CF_derives g [symbol.nonterminal A] w) :
    ∀ i : ℕ, CF_derives g [symbol.nonterminal A] (u ^ i ++ w ++ v ^ i) :=
by
  intro i
  -- First, iterate the loop i times to get [A] → u^i ++ [A] ++ v^i
  have looped := iterate_loop h_loop i

  -- Then expand the final [A] using h_base
  have expanded : CF_derives g (u ^ i ++ [symbol.nonterminal A] ++ v ^ i) (u ^ i ++ w ++ v ^ i) := by
    apply CF_deri_with_prefix_and_postfix (u ^ i) (v ^ i) h_base

  -- Chain the derivations
  exact CF_deri_of_deri_deri looped expanded

-- Helper lemma: if an injective map produces equal lists, the original lists are equal
lemma list_eq_of_map_eq {α β : Type*} {f : α → β} (hf : Function.Injective f) {l₁ l₂ : List α} :
    List.map f l₁ = List.map f l₂ → l₁ = l₂ :=
by
  intro h
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons head tail =>
      simp [List.map] at h
  | cons h₁ t₁ ih =>
    cases l₂ with
    | nil =>
      simp [List.map] at h
    | cons h₂ t₂ =>
      simp [List.map] at h
      have h_heads : h₁ = h₂ := hf h.1
      have h_tails : t₁ = t₂ := ih h.2
      rw [h_heads, h_tails]

-- Helper lemma: extract terminals from a string of symbols
lemma extract_terminals {g : CF_grammar T} (s : List (symbol T g.nt)) :
    (∀ sym ∈ s, ∃ t : T, sym = symbol.terminal t) →
    ∃ w : List T, s = List.map symbol.terminal w :=
by
  intro h
  induction s with
  | nil =>
    use []
    simp
  | cons head tail ih =>
    have head_mem : head ∈ head :: tail := by simp
    obtain ⟨t, ht⟩ := h head head_mem
    have h_tail : ∀ sym ∈ tail, ∃ t : T, sym = symbol.terminal t := by
      intro sym hmem
      have sym_mem : sym ∈ head :: tail := by simp [hmem]
      exact h sym sym_mem
    obtain ⟨w_tail, hw_tail⟩ := ih h_tail
    use t :: w_tail
    simp [ht, hw_tail]

/-- Pumping lemma for context-free languages. -/
lemma CF_pumping {T : Type} {L : Language T} (cf : is_CF L) :
  ∃ n : ℕ, ∀ w ∈ L, List.length w ≥ n → (
    ∃ u v x y z : List T,
      (w = u ++ v ++ x ++ y ++ z) ∧
      (v ++ y).length > 0         ∧
      (v ++ x ++ y).length ≤ n    ∧
      (∀ i : ℕ, u ++ v ^ i ++ x ++ y ^ i ++ z ∈ L)
  ) :=
by
  sorry
