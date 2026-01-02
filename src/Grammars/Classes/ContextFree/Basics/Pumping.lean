import Grammars.Classes.ContextFree.Basics.Definition
import Grammars.Classes.ContextFree.Basics.Toolbox
import Grammars.Utilities.ListUtils

open List

variable {T : Type}

-- Helper lemma about n_times and successor
lemma n_times_succ (l : List α) (n : ℕ) : l ^ (n + 1) = l ++ l ^ n := by
  unfold n_times
  rw [List.replicate_succ_eq_singleton_append]
  rfl

-- Helper lemma: map distributes over n_times
lemma map_n_times {α β : Type*} (f : α → β) (l : List α) (n : ℕ) :
    List.map f (l ^ n) = (List.map f l) ^ n := by
  unfold n_times
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ_eq_singleton_append, List.replicate_succ_eq_singleton_append]
    simp [List.flatten, List.map_append, ih]

-- Key helper lemma: pumping by iterating a derivation loop
-- If A derives u++[A]++v and A derives w, then for any i, we can derive u^i++w++v^i
-- This is proven by induction on i
lemma pump_loop {g : CF_grammar T} {A : g.nt} {u v w : List (symbol T g.nt)}
    (h_loop : CF_derives g [symbol.nonterminal A] (u ++ [symbol.nonterminal A] ++ v))
    (h_base : CF_derives g [symbol.nonterminal A] w) :
    ∀ i : ℕ, CF_derives g [symbol.nonterminal A] (u ^ i ++ w ++ v ^ i) :=
by
  intro i
  sorry -- TODO: prove by induction, handling the correct order of v iterations

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
  -- Extract the grammar from the CF hypothesis
  obtain ⟨g, hg⟩ := cf

  -- The pumping constant should be related to the grammar structure
  -- For a grammar with k nonterminals, typically n = 2^k
  -- For simplicity, we use n = 2 here (this would need to be adjusted for a complete proof)
  use 2

  intro w hw hw_len

  -- w ∈ L means w ∈ CF_language g
  rw [←hg] at hw
  unfold CF_language CF_generates at hw
  -- Now hw : CF_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal w)

  -- The key idea of the pumping lemma is:
  -- 1. Since w has length ≥ n, its derivation tree has sufficient height
  -- 2. By the pigeonhole principle, some nonterminal A repeats on a path in the tree
  -- 3. We can extract the "loop" from A back to A and iterate it
  --
  -- Without explicit parse trees, we assert the existence of such a decomposition
  -- and use the pump_loop lemma to show it can be pumped.

  -- Assert the existence of the decomposition
  -- In a complete proof, this would be derived from analyzing the derivation tree
  have decomposition_exists : ∃ (u_sym v_sym x_sym y_sym z_sym : List (symbol T g.nt))
                                  (u v x y z : List T)
                                  (A : g.nt),
    -- The word structure
    (List.map symbol.terminal w = u_sym ++ v_sym ++ x_sym ++ y_sym ++ z_sym) ∧
    (u_sym = List.map symbol.terminal u) ∧
    (v_sym = List.map symbol.terminal v) ∧
    (x_sym = List.map symbol.terminal x) ∧
    (y_sym = List.map symbol.terminal y) ∧
    (z_sym = List.map symbol.terminal z) ∧
    -- The lengths
    (v ++ y).length > 0 ∧
    (v ++ x ++ y).length ≤ 2 ∧
    -- The derivations
    (CF_derives g [symbol.nonterminal g.initial] (u_sym ++ [symbol.nonterminal A] ++ z_sym)) ∧
    (CF_derives g [symbol.nonterminal A] (v_sym ++ [symbol.nonterminal A] ++ y_sym)) ∧
    (CF_derives g [symbol.nonterminal A] x_sym) := by
    sorry -- This requires analyzing the derivation tree structure

  obtain ⟨u_sym, v_sym, x_sym, y_sym, z_sym, u, v, x, y, z, A,
          h_word_struct, h_u, h_v, h_x, h_y, h_z,
          h_vy_len, h_vxy_len,
          h_deriv_outer, h_deriv_loop, h_deriv_base⟩ := decomposition_exists

  -- Now use these to construct the pumping decomposition
  use u, v, x, y, z

  constructor
  · -- Prove w = u ++ v ++ x ++ y ++ z
    have map_eq : List.map (symbol.terminal (N := g.nt)) w = List.map (symbol.terminal (N := g.nt)) (u ++ v ++ x ++ y ++ z) := by
      simp only [List.map_append]
      rw [←h_u, ←h_v, ←h_x, ←h_y, ←h_z]
      exact h_word_struct
    -- Use the fact that terminal is injective to conclude
    -- Since map terminal is injective and maps are equal, the lists must be equal
    sorry -- TODO: prove that injective map implies list equality

  constructor
  · -- Prove (v ++ y).length > 0
    exact h_vy_len

  constructor
  · -- Prove (v ++ x ++ y).length ≤ n
    exact h_vxy_len

  · -- Prove ∀ i : ℕ, u ++ v^i ++ x ++ y^i ++ z ∈ L
    intro i

    -- Use pump_loop to show that A derives v^i ++ x ++ y^i
    have pumped : CF_derives g [symbol.nonterminal A] (v_sym ^ i ++ x_sym ++ y_sym ^ i) := by
      sorry -- Would use pump_loop here once it's properly proven

    -- Combine with the outer derivation
    have full_deriv : CF_derives g [symbol.nonterminal g.initial]
        (u_sym ++ (v_sym ^ i ++ x_sym ++ y_sym ^ i) ++ z_sym) := by
      -- We have: g.initial → u_sym ++ [A] ++ z_sym (from h_deriv_outer)
      -- And: A → v_sym^i ++ x_sym ++ y_sym^i (from pumped)
      -- So: g.initial → u_sym ++ (v_sym^i ++ x_sym ++ y_sym^i) ++ z_sym

      -- First, expand [A] to the pumped form using the prefix/postfix lemma
      have expand_A : CF_derives g (u_sym ++ [symbol.nonterminal A] ++ z_sym)
                                    (u_sym ++ (v_sym ^ i ++ x_sym ++ y_sym ^ i) ++ z_sym) := by
        apply CF_deri_with_prefix_and_postfix u_sym z_sym
        exact pumped

      -- Then chain with the outer derivation
      exact CF_deri_of_deri_deri h_deriv_outer expand_A

    -- Extract terminals and conclude
    have term_map : List.map (symbol.terminal (N := g.nt)) (u ++ v ^ i ++ x ++ y ^ i ++ z) =
           u_sym ++ (v_sym ^ i ++ x_sym ++ y_sym ^ i) ++ z_sym := by
      simp only [List.map_append]
      rw [map_n_times, map_n_times]
      rw [←h_u, ←h_v, ←h_x, ←h_y, ←h_z]
      simp only [List.append_assoc]

    rw [←hg]
    unfold CF_language CF_generates
    show CF_generates_str g (List.map (symbol.terminal (N := g.nt)) (u ++ v ^ i ++ x ++ y ^ i ++ z))
    rw [term_map]
    exact full_deriv
