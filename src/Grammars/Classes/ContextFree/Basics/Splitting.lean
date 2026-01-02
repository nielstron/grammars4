import Grammars.Classes.ContextFree.Basics.Toolbox


variable {T : Type}


/-- If a list x is derived from a head symbol s followed by tail symbols ss,
    then x can be split into u (derived from s) and v (derived from ss). -/
lemma head_tail_split {g : CF_grammar T}
    (x : List (symbol T g.nt))
    (s : symbol T g.nt)
    (ss : List (symbol T g.nt))
    (hyp : CF_derives g (s :: ss) x) :
  ∃ u v : List (symbol T g.nt),
    CF_derives g [s] u ∧
    CF_derives g ss v ∧
    u ++ v = x := by
  induction hyp with
  | refl =>
    -- Base case: x = s :: ss
    use [s], ss
    refine ⟨?_, ?_, ?_⟩
    · apply CF_deri_self
    · apply CF_deri_self
    · rfl
  | tail rel trans ih =>
    -- Inductive case: we have rel --[rule]--> trans and ih gives us the split for rel
    rcases ih with ⟨u, v, hu, hv, huv⟩
    rcases trans with ⟨rule, c, d, rule_in, bef, aft⟩
    have bef' : c ++ [symbol.nonterminal rule.fst] ++ d = u ++ v := by
      rw [← bef, huv]
    clear huv rel bef
    -- The rule application happens either in u or in v
    by_cases left_side : (c.length < u.length)
    · -- Case 1: Transformation happens within u
      obtain ⟨d', hd'⟩ : ∃ d', u = c ++ [symbol.nonterminal rule.fst] ++ d' ∧ d = d' ++ v := by
        have h_c_prefix : c = List.take c.length u := by
          have this1 : List.take c.length (u ++ v) = c := by
            rw [← bef']
            calc List.take c.length (c ++ [symbol.nonterminal rule.fst] ++ d)
                = List.take c.length (c ++ ([symbol.nonterminal rule.fst] ++ d)) := by rw [List.append_assoc]
              _ = List.take c.length c := by rw [List.take_append_of_le_length (Nat.le_refl _)]
              _ = c := by rw [List.take_length]
          have this2 := congr_arg (List.take c.length) bef'
          simp [List.take_append_of_le_length (Nat.le_of_lt left_side)] at this2
          exact this2
        set rest := List.drop c.length u with hrest_def
        have hu_split : u = c ++ rest := by
          calc u = List.take c.length u ++ List.drop c.length u := (List.take_append_drop c.length u).symm
               _ = c ++ rest := by rw [← h_c_prefix]
        have h_rest_eq : [symbol.nonterminal rule.fst] ++ d = rest ++ v := by
          have : c ++ [symbol.nonterminal rule.fst] ++ d = c ++ rest ++ v := by
            rw [← hu_split]; exact bef'
          have : c ++ ([symbol.nonterminal rule.fst] ++ d) = c ++ (rest ++ v) := by
            rw [← List.append_assoc, ← List.append_assoc]; exact this
          exact List.append_cancel_left this
        have hrest_nonempty : rest ≠ [] := by
          intro h
          rw [h] at h_rest_eq
          simp at h_rest_eq
          have len_eq : u.length = c.length := by rw [hu_split, h]; simp
          omega
        obtain ⟨hd_rest, tl_rest, h_rest_cons⟩ := List.exists_cons_of_ne_nil hrest_nonempty
        have h_hd : hd_rest = symbol.nonterminal rule.fst := by
          have h_cons : [symbol.nonterminal rule.fst] ++ d = (hd_rest :: tl_rest) ++ v := by
            rw [← h_rest_cons]; exact h_rest_eq
          have : symbol.nonterminal rule.fst :: d = hd_rest :: (tl_rest ++ v) := by
            simpa using h_cons
          exact List.head_eq_of_cons_eq this.symm
        use tl_rest
        constructor
        · calc u = c ++ rest := hu_split
               _ = c ++ (hd_rest :: tl_rest) := by rw [h_rest_cons]
               _ = c ++ (symbol.nonterminal rule.fst :: tl_rest) := by rw [h_hd]
               _ = c ++ [symbol.nonterminal rule.fst] ++ tl_rest := by simp
        · have h_cons : [symbol.nonterminal rule.fst] ++ d = [symbol.nonterminal rule.fst] ++ (tl_rest ++ v) := by
            calc [symbol.nonterminal rule.fst] ++ d = rest ++ v := h_rest_eq
                 _ = (hd_rest :: tl_rest) ++ v := by rw [h_rest_cons]
                 _ = (symbol.nonterminal rule.fst :: tl_rest) ++ v := by rw [h_hd]
                 _ = [symbol.nonterminal rule.fst] ++ (tl_rest ++ v) := by rfl
          exact List.append_cancel_left h_cons

      use c ++ rule.snd ++ d', v
      refine ⟨?_, ?_, ?_⟩
      · rw [hd'.1] at hu
        exact CF_deri_of_deri_tran hu ⟨rule, c, d', rule_in, rfl, rfl⟩
      · exact hv
      · calc c ++ rule.snd ++ d' ++ v = c ++ rule.snd ++ (d' ++ v) := by rw [List.append_assoc]
             _ = c ++ rule.snd ++ d := by rw [← hd'.2]
             _ = _ := aft.symm

    · -- Case 2: Transformation happens within v
      have h_u_le_c : u.length ≤ c.length := Nat.ge_of_not_lt left_side
      obtain ⟨c', hc'⟩ : ∃ c', c = u ++ c' ∧ v = c' ++ [symbol.nonterminal rule.fst] ++ d := by
        have h_u_prefix : u = List.take u.length c := by
          have this1 : List.take u.length (u ++ v) = u := List.take_left
          have this2 : c ++ [symbol.nonterminal rule.fst] ++ d = u ++ v := bef'
          calc u = List.take u.length (u ++ v) := this1.symm
               _ = List.take u.length (c ++ [symbol.nonterminal rule.fst] ++ d) := by rw [← this2]
               _ = List.take u.length (c ++ ([symbol.nonterminal rule.fst] ++ d)) := by rw [List.append_assoc]
               _ = List.take u.length c := by rw [List.take_append_of_le_length h_u_le_c]
        set c' := List.drop u.length c with hc'_def
        use c'
        constructor
        · calc c = List.take u.length c ++ List.drop u.length c := (List.take_append_drop u.length c).symm
               _ = u ++ c' := by rw [← h_u_prefix]
        · have hc_split : c = u ++ c' := by
            calc c = List.take u.length c ++ List.drop u.length c := (List.take_append_drop u.length c).symm
                 _ = u ++ c' := by rw [← h_u_prefix]
          have this1 : u ++ c' ++ [symbol.nonterminal rule.fst] ++ d = u ++ v := by
            calc u ++ c' ++ [symbol.nonterminal rule.fst] ++ d
                = c ++ [symbol.nonterminal rule.fst] ++ d := by rw [← hc_split]
              _ = u ++ v := bef'
          have h_assoc : u ++ (c' ++ [symbol.nonterminal rule.fst] ++ d) = u ++ v := by
            have : u ++ c' ++ [symbol.nonterminal rule.fst] ++ d = u ++ (c' ++ [symbol.nonterminal rule.fst] ++ d) := by
              simp [List.append_assoc]
            rw [← this]; exact this1
          have h_symm : u ++ v = u ++ (c' ++ [symbol.nonterminal rule.fst] ++ d) := h_assoc.symm
          exact List.append_cancel_left h_symm

      use u, c' ++ rule.snd ++ d
      refine ⟨?_, ?_, ?_⟩
      · exact hu
      · rw [hc'.2] at hv
        exact CF_deri_of_deri_tran hv ⟨rule, c', d, rule_in, rfl, rfl⟩
      · calc u ++ (c' ++ rule.snd ++ d)
            = u ++ c' ++ rule.snd ++ d := by simp [List.append_assoc]
          _ = c ++ rule.snd ++ d := by rw [← hc'.1]
          _ = _ := aft.symm


/-
Note: The full generalization `sequence_can_be_split` for arbitrary-length lists
can be built on top of `head_tail_split` by inducting on the list of nonterminals.
See the original `concatenation_can_be_split` in ClosureProperties/Concatenation.lean
for a similar pattern with two symbols.
-/
