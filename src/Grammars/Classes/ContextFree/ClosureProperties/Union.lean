import Grammars.Classes.ContextFree.Basics.Lifting


variable {T : Type}

private def union_grammar (g₁ g₂ : CF_grammar T) : CF_grammar T :=
CF_grammar.mk (Option (g₁.nt ⊕ g₂.nt)) none (
  (none, [symbol.nonterminal (some (Sum.inl (g₁.initial)))]) ::
  (none, [symbol.nonterminal (some (Sum.inr (g₂.initial)))]) ::
  ((List.map rule_of_rule₁ g₁.rules) ++ (List.map rule_of_rule₂ g₂.rules))
)


variable {g₁ g₂ : CF_grammar T}

section lifted_grammars

private def oN₁_of_N : (union_grammar g₁ g₂).nt → (Option g₁.nt)
| none => none
| (some (Sum.inl nonte)) => some nonte
| (some (Sum.inr _)) => none

private def oN₂_of_N : (union_grammar g₁ g₂).nt → (Option g₂.nt)
| none => none
| (some (Sum.inl _)) => none
| (some (Sum.inr nonte)) => some nonte


private def g₁g : @lifted_grammar T :=
lifted_grammar.mk g₁ (union_grammar g₁ g₂) (some ∘ Sum.inl)
  (by
    intro x y h
    cases h
    rfl
  )
  (by
    intro r h
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    rw [List.mem_map]
    refine ⟨r, h, ?_⟩
    unfold rule_of_rule₁
    unfold lift_rule
    norm_num
    unfold lift_string
    unfold lsTN_of_lsTN₁
    five_steps
  )
  oN₁_of_N
  (by
    intro x y ass
    cases x with
    | none =>
        right
        rfl
    | some x =>
        cases x with
        | inl x =>
            cases y with
            | none =>
                right
                rfl
            | some y =>
                cases y with
                | inl y =>
                    left
                    simp [oN₁_of_N] at ass
                    cases ass
                    rfl
                | inr y =>
                    simp [oN₁_of_N] at ass
                    cases ass
        | inr x =>
            right
            rfl
  )
  (by
    intro r
    rintro ⟨r_in, r_ntype⟩
    cases r_in with
    | head =>
        exfalso
        rw [r_in] at r_ntype
        dsimp only at r_ntype
        cases r_ntype with
        | intro n₀ imposs =>
            exact Option.no_confusion imposs
    | tail r_in =>
        cases r_in with
        | head =>
            exfalso
            rw [r_in] at r_ntype
            dsimp only at r_ntype
            cases r_ntype with
            | intro n₀ imposs =>
                exact Option.no_confusion imposs
        | tail r_in =>
            change r ∈ (List.map rule_of_rule₁ g₁.rules ++ List.map rule_of_rule₂ g₂.rules) at r_in
            rw [List.mem_append] at r_in
            cases r_in with
            | inl r_in =>
                rw [List.mem_map] at r_in
                rcases r_in with ⟨r₁, r₁_in, r₁_convert_r⟩
                refine ⟨r₁, r₁_in, ?_⟩
                rw [←r₁_convert_r]
                simp only [
                  lift_rule, rule_of_rule₁, lift_string, lsTN_of_lsTN₁,
                  Prod.mk.inj_iff, eq_self_iff_true, true_and
                ]
                five_steps
            | inr r_in =>
                exfalso
                rw [List.mem_map] at r_in
                rcases r_in with ⟨r₂, r₂_in, r₂_convert_r⟩
                rw [←r₂_convert_r] at r_ntype
                unfold rule_of_rule₂ at r_ntype
                dsimp only at r_ntype
                cases r_ntype with
                | intro n₁ contr =>
                    rw [Option.some_inj] at contr
                    exact Sum.noConfusion contr
  )
  (by
    intro
    rfl
  )

private def g₂g : @lifted_grammar T :=
lifted_grammar.mk g₂ (union_grammar g₁ g₂) (some ∘ Sum.inr)
  (by
    intro x y h
    cases h
    rfl
  )
  (by
    intro r h
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_append_right
    rw [List.mem_map]
    refine ⟨r, h, ?_⟩
    unfold rule_of_rule₂
    unfold lift_rule
    norm_num
    unfold lift_string
    unfold lsTN_of_lsTN₂
    five_steps
  )
  oN₂_of_N
  (by
    intro x y ass
    cases x with
    | none =>
        right
        rfl
    | some x =>
        cases x with
        | inl x =>
            right
            rfl
        | inr x =>
            cases y with
            | none =>
                right
                rfl
            | some y =>
                cases y with
                | inl y =>
                    simp [oN₂_of_N] at ass
                    cases ass
                | inr y =>
                    left
                    simp [oN₂_of_N] at ass
                    cases ass
                    rfl
  )
  (by
    intro r
    rintro ⟨r_in, r_ntype⟩
    cases List.eq_or_mem_of_mem_cons r_in with
    | inl r_eq =>
        exfalso
        rw [r_eq] at r_ntype
        dsimp only at r_ntype
        cases r_ntype with
        | intro n₀ imposs =>
            exact Option.no_confusion imposs
    | inr r_in_ =>
        cases List.eq_or_mem_of_mem_cons r_in_ with
        | inl r_eq_ =>
            exfalso
            rw [r_eq_] at r_ntype
            dsimp only at r_ntype
            cases r_ntype with
            | intro n₀ imposs =>
                exact Option.no_confusion imposs
        | inr r_in__ =>
            rw [List.mem_append] at r_in__
            cases r_in__ with
            | inl r_in =>
                exfalso
                rw [List.mem_map] at r_in
                rcases r_in with ⟨r₁, r₁_in, r₁_convert_r⟩
                rw [←r₁_convert_r] at r_ntype
                unfold rule_of_rule₁ at r_ntype
                dsimp only at r_ntype
                cases r_ntype with
                | intro n₂ contr =>
                    rw [Option.some_inj] at contr
                    exact Sum.noConfusion contr
            | inr r_in =>
                rw [List.mem_map] at r_in
                rcases r_in with ⟨r₂, r₂_in, r₂_convert_r⟩
                refine ⟨r₂, r₂_in, ?_⟩
                rw [←r₂_convert_r]
                simp only [
                  lift_rule, rule_of_rule₂, lift_string, lsTN_of_lsTN₂,
                  Prod.mk.inj_iff, eq_self_iff_true, true_and
                ]
                five_steps
  )
  (by
    intro
    rfl
  )

end lifted_grammars


section lemmata_subset

private lemma deri₁_more (w : List (symbol T g₁.nt)) :
  CF_derives g₁ [symbol.nonterminal g₁.initial] w →
    CF_derives
      (union_grammar g₁ g₂)
      (lsTN_of_lsTN₁ [symbol.nonterminal g₁.initial])
      (lsTN_of_lsTN₁ w) :=
by
  intro ass
  let gg₁ := @g₁g T g₁ g₂
  change CF_derives gg₁.g (lsTN_of_lsTN₁ [symbol.nonterminal g₁.initial]) (lsTN_of_lsTN₁ w)
  have techni : lsTN_of_lsTN₁ = lift_string gg₁.lift_nt := by
    unfold lsTN_of_lsTN₁
    unfold lift_string
    ext1 w
    five_steps
  rw [techni]
  exact lift_deri ass

private lemma deri₂_more (w : List (symbol T g₂.nt)) :
  CF_derives g₂ [symbol.nonterminal g₂.initial] w →
    CF_derives
      (union_grammar g₁ g₂)
      (lsTN_of_lsTN₂ [symbol.nonterminal g₂.initial])
      (lsTN_of_lsTN₂ w) :=
by
  intro ass
  let gg₂ := @g₂g T g₁ g₂
  change CF_derives gg₂.g (lsTN_of_lsTN₂ [symbol.nonterminal g₂.initial]) (lsTN_of_lsTN₂ w)
  have techni : lsTN_of_lsTN₂ = lift_string gg₂.lift_nt := by
    unfold lsTN_of_lsTN₂
    unfold lift_string
    ext1 w
    five_steps
  rw [techni]
  exact lift_deri ass

private lemma in_union_of_in_first (w : List T) :
  w ∈ CF_language g₁  →  w ∈ CF_language (union_grammar g₁ g₂)  :=
by
  intro assum

  have deri_start :
    CF_derives
      (union_grammar g₁ g₂)
      [symbol.nonterminal none]
      [symbol.nonterminal (some (Sum.inl g₁.initial))],
  := by
    apply CF_deri_of_tran
    refine ⟨(none, [symbol.nonterminal (some (Sum.inl (g₁.initial)))]), ?_, ?_, ?_⟩
    ·
      change (none, [symbol.nonterminal (some (Sum.inl g₁.initial))]) ∈ (
        (none, [symbol.nonterminal (some (Sum.inl (g₁.initial)))]) ::
        (none, [symbol.nonterminal (some (Sum.inr (g₂.initial)))]) ::
        (List.map rule_of_rule₁ g₁.rules ++ List.map rule_of_rule₂ g₂.rules)
      )
      apply List.mem_cons_self
    ·
      exact []
    ·
      exact []

  have deri_rest :
    CF_derives
      (union_grammar g₁ g₂)
      [symbol.nonterminal (some (Sum.inl g₁.initial))]
      (List.map symbol.terminal w),
  := by
    have beginning :
      [symbol.nonterminal (some (Sum.inl g₁.initial))] =
      lsTN_of_lsTN₁ [symbol.nonterminal g₁.initial] := by
      unfold lsTN_of_lsTN₁
      change
        [symbol.nonterminal (some (Sum.inl g₁.initial))] =
        [sTN_of_sTN₁ (symbol.nonterminal g₁.initial)]
      unfold sTN_of_sTN₁
    have ending :
      List.map symbol.terminal w =
      lsTN_of_lsTN₁ (List.map symbol.terminal w) := by
      simp [lsTN_of_lsTN₁, sTN_of_sTN₁, List.map_map]
    rw [beginning, ending]
    exact deri₁_more (List.map symbol.terminal w) assum

  unfold CF_language
  rw [Set.mem_setOf_eq]
  unfold CF_generates
  unfold CF_generates_str
  unfold CF_derives
  apply CF_deri_of_deri_deri deri_start
  exact deri_rest

private lemma in_union_of_in_second (w : List T) :
  w ∈ CF_language g₂  →  w ∈ CF_language (union_grammar g₁ g₂)  :=
by
  intro assum

  have deri_start :
    CF_derives
      (union_grammar g₁ g₂)
      [symbol.nonterminal none]
      [symbol.nonterminal (some (Sum.inr g₂.initial))],
  := by
    apply CF_deri_of_tran
    refine ⟨(none, [symbol.nonterminal (some (Sum.inr (g₂.initial)))]), ?_, ?_, ?_⟩
    ·
      change (none, [symbol.nonterminal (some (Sum.inr g₂.initial))]) ∈ (
        (none, [symbol.nonterminal (some (Sum.inl (g₁.initial)))]) ::
        (none, [symbol.nonterminal (some (Sum.inr (g₂.initial)))]) ::
        (List.map rule_of_rule₁ g₁.rules ++ List.map rule_of_rule₂ g₂.rules)
      )
      apply List.mem_cons_of_mem
      apply List.mem_cons_self
    ·
      exact []
    ·
      exact []

  have deri_rest :
    CF_derives
      (union_grammar g₁ g₂)
      [symbol.nonterminal (some (Sum.inr g₂.initial))]
      (List.map symbol.terminal w),
  := by
    have beginning :
      [symbol.nonterminal (some (Sum.inr g₂.initial))] =
      lsTN_of_lsTN₂ [symbol.nonterminal g₂.initial] := by
      unfold lsTN_of_lsTN₂
      change
        [symbol.nonterminal (some (Sum.inr g₂.initial))] =
        [sTN_of_sTN₂ (symbol.nonterminal g₂.initial)]
      unfold sTN_of_sTN₂
    have ending :
      List.map symbol.terminal w =
      lsTN_of_lsTN₂ (List.map symbol.terminal w) := by
      simp [lsTN_of_lsTN₂, sTN_of_sTN₂, List.map_map]
    rw [beginning, ending]
    exact deri₂_more (List.map symbol.terminal w) assum

  unfold CF_language
  rw [Set.mem_setOf_eq]
  unfold CF_generates
  unfold CF_generates_str
  unfold CF_derives
  apply CF_deri_of_deri_deri deri_start
  exact deri_rest

end lemmata_subset


section lemmata_supset

macro "good_singleton" : tactic =>
  `(tactic|
    unfold good_string
    intro a in_singleton
    rw [List.mem_singleton] at in_singleton
    rw [in_singleton]
    unfold good_letter
  )

private lemma in_language_left_case_of_union {w : List T}
    (hypo : CF_derives (union_grammar g₁ g₂)
      [symbol.nonterminal (some (Sum.inl g₁.initial))]
      (List.map symbol.terminal w)) :
  w ∈ CF_language g₁ :=
by
  unfold CF_language
  rw [Set.mem_setOf_eq]
  unfold CF_generates
  unfold CF_generates_str

  let gg₁ := @g₁g T g₁ g₂

  have bar :
    [symbol.nonterminal g₁.initial] =
    (sink_string gg₁.sink_nt [symbol.nonterminal (some (Sum.inl g₁.initial))]),
  := by
    unfold sink_string
    rfl
  rw [bar]

  have baz : List.map symbol.terminal w = sink_string gg₁.sink_nt (List.map symbol.terminal w),
  := by
    unfold sink_string
    rw [List.filterMap_map]
    change List.map symbol.terminal w =
      List.filterMap (fun x => (sink_symbol gg₁.sink_nt ∘ symbol.terminal) x) w
    convert_to List.map symbol.terminal w = List.filterMap (fun x => Option.some (symbol.terminal x)) w
    change List.map symbol.terminal w = List.filterMap (Option.some ∘ symbol.terminal) w
    clear hypo
    induction w with
    | nil =>
        rfl
    | cons d l ih =>
        simp [List.filterMap, ih]
  rw [baz]

  exact (sink_deri gg₁ [symbol.nonterminal (some (Sum.inl g₁.initial))] (List.map symbol.terminal w) hypo (by
    good_singleton
    refine ⟨g₁.initial, rfl⟩
  )).left

private lemma in_language_right_case_of_union {w : List T}
    (hypo : CF_derives (union_grammar g₁ g₂)
      [symbol.nonterminal (some (Sum.inr g₂.initial))]
      (List.map symbol.terminal w)) :
  w ∈ CF_language g₂ :=
by
  unfold CF_language
  rw [Set.mem_setOf_eq]
  unfold CF_generates
  unfold CF_generates_str

  let gg₂ := @g₂g T g₁ g₂

  have bar :
    [symbol.nonterminal g₂.initial] =
    (sink_string gg₂.sink_nt [symbol.nonterminal (some (Sum.inr g₂.initial))]),
  := by
    unfold sink_string
    rfl
  rw [bar]

  have baz : List.map symbol.terminal w = sink_string gg₂.sink_nt (List.map symbol.terminal w),
  := by
    unfold sink_string
    rw [List.filterMap_map]
    change List.map symbol.terminal w =
      List.filterMap (fun x => (sink_symbol gg₂.sink_nt ∘ symbol.terminal) x) w
    convert_to List.map symbol.terminal w = List.filterMap (fun x => Option.some (symbol.terminal x)) w
    change List.map symbol.terminal w = List.filterMap (Option.some ∘ symbol.terminal) w
    clear hypo
    induction w with
    | nil =>
        rfl
    | cons d l ih =>
        simp [List.filterMap, ih]
  rw [baz]

  exact (sink_deri gg₂ [symbol.nonterminal (some (Sum.inr g₂.initial))] (List.map symbol.terminal w) hypo (by
    good_singleton
    refine ⟨g₂.initial, rfl⟩
  )).left

private lemma both_empty
    (u v: List (symbol T (union_grammar g₁ g₂).nt))
    (a : (symbol T (union_grammar g₁ g₂).nt))
    (bef: [symbol.nonterminal (union_grammar g₁ g₂).initial] = u ++ [a] ++ v) :
  u = []  ∧  v = [] :=
by
  have len := congr_arg List.length bef
  rw [List.length_singleton, List.length_append, List.length_append, List.length_singleton] at len
  refine And.intro ?_ ?_
  ·
    by_contra h
    rw [←List.length_eq_zero] at h
    exact Nat.not_succ_le_self 1 (by
      calc
        1 = (u.length + 1) + v.length := len
        _ = u.length + (1 + v.length) := add_assoc (List.length u) 1 (List.length v)
        _ ≥ 1 + (1 + v.length) := add_le_add (Nat.one_le_iff_ne_zero.mpr h) (le_of_eq rfl)
        _ = (1 + 1) + v.length := (add_assoc 1 1 (List.length v)).symm
        _ ≥ 1 + 1 + 0 := le_self_add
        _ = 2 := rfl
    )
  ·
    by_contra h
    rw [←List.length_eq_zero] at h
    exact Nat.not_succ_le_self 1 (by
      calc
        1 = (u.length + 1) + v.length := len
        _ ≥ (u.length + 1) + 1 := add_le_add (le_of_eq rfl) (Nat.one_le_iff_ne_zero.mpr h)
        _ = u.length + (1 + 1) := add_assoc (List.length u) 1 1
        _ ≥ 0 + (1 + 1) := le_add_self
        _ = (0 + 1) + 1 := (add_assoc 0 1 1).symm
        _ = 2 := rfl
    )

private lemma in_language_impossible_case_of_union
    (w : List T)
    (r : (union_grammar g₁ g₂).nt × List (symbol T (union_grammar g₁ g₂).nt))
    (u v: List (symbol T (union_grammar g₁ g₂).nt))
    (hu : u = []) (hv : v = [])
    (bef: [symbol.nonterminal (union_grammar g₁ g₂).initial] = u ++ [symbol.nonterminal r.fst] ++ v)
    (sbi : r ∈ (List.map rule_of_rule₁ g₁.rules ++ List.map rule_of_rule₂ g₂.rules)) :
  w ∈ CF_language g₁ ∨ w ∈ CF_language g₂ :=
by
  exfalso
  rw [hu, hv] at bef
  rw [List.nil_append, List.append_nil] at bef
  change [symbol.nonterminal none] = [symbol.nonterminal r.fst] at bef
  have rule_root : r.fst = none := by
    have almost := List.head_eq_of_cons_eq bef
    exact symbol.nonterminal.inj almost.symm
  rw [List.mem_append] at sbi
  cases sbi with
  | inl sbi =>
      rw [List.mem_map] at sbi
      rcases sbi with ⟨r₁, _, imposs⟩
      unfold rule_of_rule₁ at imposs
      rw [←imposs] at rule_root
      unfold Prod.fst at rule_root
      exact Option.no_confusion rule_root
  | inr sbi =>
      rw [List.mem_map] at sbi
      rcases sbi with ⟨r₂, _, imposs⟩
      unfold rule_of_rule₂ at imposs
      rw [←imposs] at rule_root
      unfold Prod.fst at rule_root
      exact Option.no_confusion rule_root

private lemma in_language_of_in_union (w : List T) :
  w ∈ CF_language (union_grammar g₁ g₂)   →   w ∈ CF_language g₁  ∨  w ∈ CF_language g₂   :=
by
  intro ass

  cases CF_tran_or_id_of_deri ass with
  | inl impossible =>
      exfalso
      have zeroth := congr_arg (fun p => List.nth p 0) impossible
      unfold List.nth at zeroth
      rw [List.nth_map] at zeroth
      cases w.nth 0 with
      | none =>
          rw [Option.map_none'] at zeroth
          exact Option.no_confusion zeroth
      | some =>
          rw [Option.map_some'] at zeroth
          exact symbol.no_confusion (Option.some.inj zeroth)
  | inr h =>
      rcases h with ⟨S₁, deri_head, deri_tail⟩
      rcases deri_head with ⟨rule, ruleok, u, v, h_bef, h_aft⟩

      rw [h_aft] at deri_tail
      cases both_empty u v (symbol.nonterminal rule.fst) h_bef with
      | intro u_nil v_nil =>
          cases ruleok with
          | inl g₁S =>
              left
              rw [g₁S] at *
              rw [u_nil, v_nil, List.nil_append] at deri_tail
              exact in_language_left_case_of_union deri_tail
          | inr r_rest =>
              cases r_rest with
              | inl g₂S =>
                  right
                  rw [g₂S] at *
                  rw [u_nil, v_nil, List.nil_append] at deri_tail
                  exact in_language_right_case_of_union deri_tail
              | inr r_imposs =>
                  exact in_language_impossible_case_of_union w rule u v u_nil v_nil h_bef r_imposs

end lemmata_supset


/-- The class of context-free languages is closed under union. -/
theorem CF_of_CF_u_CF {T : Type} (L₁ : Language T) (L₂ : Language T) :
  is_CF L₁  ∧  is_CF L₂   →   is_CF (L₁ + L₂)   :=
by
  rintro ⟨⟨g₁, eq_L₁⟩, ⟨g₂, eq_L₂⟩⟩

  refine ⟨union_grammar g₁ g₂, ?_⟩

  apply Set.eq_of_subset_of_subset
  ·
    -- prove `L₁ + L₂ ⊇ `
    intro w hyp
    rw [Language.mem_add]
    rw [←eq_L₁]
    rw [←eq_L₂]
    exact in_language_of_in_union w hyp
  ·
    -- prove `L₁ + L₂ ⊆ `
    intro w hyp
    cases hyp with
    | inl case₁ =>
        rw [←eq_L₁] at case₁
        exact in_union_of_in_first w case₁
    | inr case₂ =>
        rw [←eq_L₂] at case₂
        exact in_union_of_in_second w case₂
