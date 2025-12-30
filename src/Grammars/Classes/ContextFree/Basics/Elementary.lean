import Grammars.Classes.ContextFree.Basics.Toolbox
import Grammars.Utilities.ListUtils
import Grammars.Utilities.WrittenByOthers.TrimAssoc

variable {T : Type}


/-- Context-free grammar for the empty Language (i.e., `∈` always gives `false`). -/
def cfg_empty_lang : CF_grammar T :=
CF_grammar.mk (Fin 1) 0 []

/-- Characterization of the empty Language. -/
lemma language_of_cfg_empty_lang :
  CF_language (@cfg_empty_lang T) = 0 :=
by
  unfold CF_language
  ext w
  constructor
  ·
    intro hw
    have : False := by
      change CF_derives cfg_empty_lang [symbol.nonterminal cfg_empty_lang.initial]
        (List.map symbol.terminal w) at hw
      cases CF_tran_or_id_of_deri hw with
      | inl h =>
        cases w with
        | nil =>
          cases h
        | cons head tail =>
          cases h
      | inr h =>
        rcases h with ⟨v, hstep, _⟩
        rcases hstep with ⟨r, u, v', rin, _, _⟩
        cases rin
    simpa using this
  ·
    intro hw
    cases hw

/-- Context-free grammar for the singleton Language that contains `[]` as its only word. -/
def cfg_empty_word : CF_grammar T :=
CF_grammar.mk (Fin 1) 0 [(0, [])]

/-- Characterization of the singleton Language. -/
lemma language_of_cfg_empty_word :
  CF_language (@cfg_empty_word T) = singleton [] :=
by
  unfold CF_language
  ext w
  constructor
  ·
    intro hw
    change
      CF_derives
        (@cfg_empty_word T)
        [symbol.nonterminal (@cfg_empty_lang T).initial]
        (List.map symbol.terminal w)
      at hw
    cases
      @CF_tran_or_id_of_deri T
        (@cfg_empty_word T)
        [symbol.nonterminal cfg_empty_lang.initial]
        (List.map symbol.terminal w)
        hw with
    | inl h =>
      exfalso
      cases w with
      | nil =>
        cases h
      | cons head tail =>
        cases h
    | inr h =>
      rcases h with ⟨v, step_init, step_none⟩
      have v_is_empty_word : v = List.nil := by
        rcases step_init with ⟨r, pre, pos, rin, bef, aft⟩
        have rule : r = ((0 : Fin 1), []) := by
          rw [←List.mem_singleton]
          exact rin
        have empty_surrounding : pre = [] ∧ pos = [] := by
          rw [rule] at bef
          have bef_lengths := congr_arg List.length bef
          simp [List.length_append] at bef_lengths
          have pre_zero : pre.length = 0 := by
            linarith
          have pos_zero : pos.length = 0 := by
            linarith
          have pre_nil : pre = [] := by
            simpa [List.length_eq_zero_iff] using pre_zero
          have pos_nil : pos = [] := by
            simpa [List.length_eq_zero_iff] using pos_zero
          exact ⟨pre_nil, pos_nil⟩
        rw [empty_surrounding.1, empty_surrounding.2] at aft
        rw [rule] at aft
        exact aft
      rw [v_is_empty_word] at step_none
      cases
        @CF_tran_or_id_of_deri T
          (@cfg_empty_word T)
          List.nil
          (List.map symbol.terminal w)
          step_none with
      | inl h =>
        by_contra contra
        have w_not_nil : w.length > 0 := by
          apply List.length_pos_of_ne_nil
          simpa using contra
        have impossible_lengths := congr_arg List.length h
        rw [List.length] at impossible_lengths
        rw [List.length_map] at impossible_lengths
        rw [←impossible_lengths] at w_not_nil
        exact Nat.lt_irrefl 0 w_not_nil
      | inr h =>
        exfalso
        rcases h with ⟨v1, ⟨r1, pre1, pos1, r1_in, impossible, _⟩, _⟩
        have impossible_len := congr_arg List.length impossible
        rw [List.length_append_append] at impossible_len
        rw [List.length_singleton] at impossible_len
        rw [List.length] at impossible_len
        have hzero : (0 : Nat) = pre1.length + 1 + pos1.length := by
          simpa using impossible_len
        have hsucc : (0 : Nat) = Nat.succ (pre1.length + pos1.length) := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hzero
        exact (Nat.succ_ne_zero _ hsucc.symm)
  ·
    intro hyp
    rw [Set.mem_singleton_iff] at hyp
    change CF_derives cfg_empty_word [symbol.nonterminal cfg_empty_word.initial]
      (List.map symbol.terminal w)
    apply @CF_deri_of_tran
    refine ⟨((0 : Fin 1), []), [], [], ?_, ?_, ?_⟩
    · simp [cfg_empty_word]
    · simp [cfg_empty_word]
    · simp [hyp, cfg_empty_word]

/-- Context-free grammar for a Language `{a}.star` where `a` is a given terminal symbol. -/
def cfg_symbol_star (a : T) : CF_grammar T :=
CF_grammar.mk (Fin 1) 0 [(0, [symbol.terminal a, symbol.nonterminal 0]), (0, [])]

/-- Characterization of the `{a}.star` Language. -/
lemma language_of_cfg_symbol_star (a : T) :
  CF_language (cfg_symbol_star a) = fun w => ∃ n : ℕ, w = List.replicate n a :=
by
  ext w
  constructor
  ·
    intro hw
    /-
      We prove this inclusion as follows:
      (1) `w ∈ CF_language (cfg_symbol_star a)` →
      (2) `w` contains only `a`s →
      (3) `∃ (n : ℕ), w = List.replicate n a)` □
    -/
    have implication2 : (∀ t : T, t ≠ a → t ∉ w) → (∃ (n : ℕ), w = List.replicate n a) := by
      intro h
      have hmem : ∀ b ∈ w, b = a := by
        intro b hb
        by_contra hba
        exact (h b hba) hb
      refine ⟨w.length, ?_⟩
      simpa using (List.eq_replicate_of_mem (l := w) (a := a) hmem)
    have implication1 : w ∈ CF_language (cfg_symbol_star a) → (∀ t : T, t ≠ a → t ∉ w) := by
      clear implication2
      intro ass t nq
      change CF_generates_str (cfg_symbol_star a) (List.map symbol.terminal w) at ass
      unfold CF_generates_str at ass
      have indu :
        ∀ v : List (symbol T (cfg_symbol_star a).nt),
          CF_derives (cfg_symbol_star a)
            [symbol.nonterminal (cfg_symbol_star a).initial] v →
              symbol.terminal t ∉ v := by
        intro v hyp
        induction hyp with
        | refl =>
          intro hmem
          rw [List.mem_singleton] at hmem
          cases hmem
        | tail _ step ih =>
          rcases step with ⟨r, u, v, r_in, h_bef, h_aft⟩
          have ih' : symbol.terminal t ∉ u ++ [symbol.nonterminal r.1] ++ v := by
            simpa [h_bef] using ih
          have hu : symbol.terminal t ∉ u := by
            intro hmem
            apply ih'
            simp [List.mem_append, hmem]
          have hv : symbol.terminal t ∉ v := by
            intro hmem
            apply ih'
            simp [List.mem_append, hmem]
          have hr2 : symbol.terminal t ∉ r.2 := by
            have r_in' :
                r = ((0 : Fin 1), [symbol.terminal a, symbol.nonterminal (0 : Fin 1)]) ∨
                  r = ((0 : Fin 1), ([] : List (symbol T (cfg_symbol_star a).nt))) := by
              simpa [cfg_symbol_star] using r_in
            cases r_in' with
            | inl h =>
              rw [h]
              intro hmem
              have hmem' :
                  (@symbol.terminal T (cfg_symbol_star a).nt t) =
                    (@symbol.terminal T (cfg_symbol_star a).nt a) ∨
                  (@symbol.terminal T (cfg_symbol_star a).nt t) =
                    symbol.nonterminal (0 : Fin 1) := by
                simpa [List.mem_cons] using hmem
              cases hmem' with
              | inl hmem'' =>
                apply nq
                cases hmem''
                rfl
              | inr hmem'' =>
                cases hmem''
            | inr h =>
              rw [h]
              simp
          intro hmem
          rw [h_aft] at hmem
          simp [List.mem_append, hu, hr2, hv] at hmem
      specialize indu (List.map symbol.terminal w) ass
      intro hmem
      exact indu (List.mem_map_of_mem (f := symbol.terminal) hmem)
    exact implication2 (implication1 hw)
  ·
    intro hw
    rcases hw with ⟨n, hwn⟩
    rw [hwn]
    convert_to CF_generates_str (cfg_symbol_star a) (List.map symbol.terminal (List.replicate n a))
    unfold CF_generates_str
    clear hwn w
    have comes_to :
      CF_derives
        (cfg_symbol_star a)
        [symbol.nonterminal (cfg_symbol_star a).initial]
        (List.replicate n (symbol.terminal a) ++ [symbol.nonterminal (0 : Fin 1)]) := by
      induction n with
      | zero =>
        apply CF_deri_self
      | succ n ih =>
        apply CF_deri_of_deri_tran ih
        refine ⟨((0 : Fin 1), [symbol.terminal a, symbol.nonterminal (0 : Fin 1)]),
          List.replicate n (symbol.terminal a), [], ?_, ?_, ?_⟩
        · apply List.mem_cons_self
        ·
          rw [List.append_nil]
        ·
          rw [List.append_nil]
          change
            (@symbol.terminal T (cfg_symbol_star a).nt a) ::
                (List.replicate n (@symbol.terminal T (cfg_symbol_star a).nt a) ++
                  [symbol.nonterminal (0 : Fin 1)]) =
              List.replicate n (@symbol.terminal T (cfg_symbol_star a).nt a) ++
                ([@symbol.terminal T (cfg_symbol_star a).nt a] ++ [symbol.nonterminal (0 : Fin 1)])
          rw [←List.cons_append]
          simp [List.append_assoc]
          have count_succ_left :
              @symbol.terminal T (cfg_symbol_star a).nt a ::
                List.replicate n (@symbol.terminal T (cfg_symbol_star a).nt a) =
                  List.replicate (n + 1) (@symbol.terminal T (cfg_symbol_star a).nt a) := by
            simp [List.replicate_succ, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc]
          have count_succ_right :
              List.replicate n (@symbol.terminal T (cfg_symbol_star a).nt a) ++
                [@symbol.terminal T (cfg_symbol_star a).nt a] =
                  List.replicate (n + 1) (@symbol.terminal T (cfg_symbol_star a).nt a) := by
            change
              List.replicate n (@symbol.terminal T (cfg_symbol_star a).nt a) ++
                List.replicate 1 (@symbol.terminal T (cfg_symbol_star a).nt a) =
                  List.replicate (n + 1) (@symbol.terminal T (cfg_symbol_star a).nt a)
            simpa using (List.replicate_append_replicate (n := n) (m := 1) (a := symbol.terminal a))
          calc
            @symbol.terminal T (cfg_symbol_star a).nt a ::
                (List.replicate n (@symbol.terminal T (cfg_symbol_star a).nt a) ++
                  [symbol.nonterminal (0 : Fin 1)]) =
                (@symbol.terminal T (cfg_symbol_star a).nt a ::
                  List.replicate n (@symbol.terminal T (cfg_symbol_star a).nt a)) ++
                  [symbol.nonterminal (0 : Fin 1)] := by
                    simp [List.cons_append]
            _ =
                List.replicate (n + 1) (@symbol.terminal T (cfg_symbol_star a).nt a) ++
                  [symbol.nonterminal (0 : Fin 1)] := by
                    simpa [count_succ_left]
            _ =
                (List.replicate n (@symbol.terminal T (cfg_symbol_star a).nt a) ++
                  [@symbol.terminal T (cfg_symbol_star a).nt a]) ++
                  [symbol.nonterminal (0 : Fin 1)] := by
                    simpa [count_succ_right]
            _ =
                List.replicate n (@symbol.terminal T (cfg_symbol_star a).nt a) ++
                  [@symbol.terminal T (cfg_symbol_star a).nt a, symbol.nonterminal (0 : Fin 1)] := by
                    simp [List.append_assoc]
    apply CF_deri_of_deri_tran comes_to
    refine ⟨((0 : Fin 1), []), List.replicate n (symbol.terminal a), [], ?_, ?_, ?_⟩
    ·
      apply List.mem_cons_of_mem
      apply List.mem_cons_self
    ·
      rw [List.append_nil]
    ·
      simpa [List.append_nil, List.map_replicate]
