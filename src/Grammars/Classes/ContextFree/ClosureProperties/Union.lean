import Grammars.Classes.ContextFree.Basics.Lifting


variables {T : Type}

private def union_grammar (g₁ g₂ : CF_grammar T) : CF_grammar T :=
CF_grammar.mk (Option (g₁.nt ⊕ g₂.nt)) none (
  (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) ::
  (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) ::
  ((List.map rule_of_rule₁ g₁.rules) ++ (List.map rule_of_rule₂ g₂.rules))
)


variables {g₁ g₂ : CF_grammar T}

section lifted_grammars

private def oN₁_of_N : (union_grammar g₁ g₂).nt → (Option g₁.nt)
| none := none
| (some (sum.inl nonte)) := some nonte
| (some (sum.inr _)) := none

private def oN₂_of_N : (union_grammar g₁ g₂).nt → (Option g₂.nt)
| none := none
| (some (sum.inl _)) := none
| (some (sum.inr nonte)) := some nonte


private def g₁g : @lifted_grammar T :=
lifted_grammar.mk g₁ (union_grammar g₁ g₂) (some ∘ sum.inl) (by {
  intros x y h,
  apply sum.inl_injective,
  apply Option.some_injective,
  exact h,
}) (by {
  intros r h,
  apply List.mem_cons_of_mem,
  apply List.mem_cons_of_mem,
  apply List.mem_append_left,
  rw List.mem_map,
  use r,
  split,
  {
    exact h,
  },
  unfold rule_of_rule₁,
  unfold lift_rule,
  norm_num,
  unfold lift_string,
  unfold lsTN_of_lsTN₁,
  five_steps,
}) oN₁_of_N (by {
  intros x y ass,
  cases x,
  {
    right,
    refl,
  },
  cases x, swap,
  {
    right,
    refl,
  },
  cases y,
  {
    rw ass,
    right,
    refl,
  },
  cases y, swap,
  {
    tauto,
  },
  left,
  simp only [oN₁_of_N] at ass,
  apply congr_arg,
  apply congr_arg,
  exact ass,
}) (by {
  intro r,
  rintro ⟨r_in, r_ntype⟩,
  cases r_in,
  {
    exfalso,
    rw r_in at r_ntype,
    dsimp only at r_ntype,
    cases r_ntype with n₀ imposs,
    exact Option.no_confusion imposs,
  },
  cases r_in,
  {
    exfalso,
    rw r_in at r_ntype,
    dsimp only at r_ntype,
    cases r_ntype with n₀ imposs,
    exact Option.no_confusion imposs,
  },
  change r ∈ (List.map rule_of_rule₁ g₁.rules ++ List.map rule_of_rule₂ g₂.rules) at r_in,
  rw List.mem_append at r_in,
  cases r_in,
  {
    rw List.mem_map at r_in,
    rcases r_in with ⟨r₁, r₁_in, r₁_convert_r⟩,
    use r₁,
    split,
    {
      exact r₁_in,
    },
    rw ←r₁_convert_r,
    simp only [
      lift_rule, rule_of_rule₁, lift_string, lsTN_of_lsTN₁,
      prod.mk.inj_iff, eq_self_iff_true, true_and
    ],
    five_steps,
  },
  {
    exfalso,
    rw List.mem_map at r_in,
    rcases r_in with ⟨r₂, r₂_in, r₂_convert_r⟩,
    rw ←r₂_convert_r at r_ntype,
    unfold rule_of_rule₂ at r_ntype,
    dsimp only at r_ntype,
    cases r_ntype with n₁ contr,
    rw Option.some_inj at contr,
    exact sum.no_confusion contr,
  },
}) (by { intro, refl })

private def g₂g : @lifted_grammar T :=
lifted_grammar.mk g₂ (union_grammar g₁ g₂) (some ∘ sum.inr) (by {
  intros x y h,
  apply sum.inr_injective,
  apply Option.some_injective,
  exact h,
}) (by {
  intros r h,
  apply List.mem_cons_of_mem,
  apply List.mem_cons_of_mem,
  apply List.mem_append_right,
  rw List.mem_map,
  use r,
  split,
  {
    exact h,
  },
  unfold rule_of_rule₂,
  unfold lift_rule,
  norm_num,
  unfold lift_string,
  unfold lsTN_of_lsTN₂,
  five_steps,
}) oN₂_of_N (by {
  intros x y ass,
  cases x,
  {
    right,
    refl,
  },
  cases x,
  {
    right,
    refl,
  },
  cases y,
  {
    right,
    rw ass,
    refl,
  },
  cases y,
  {
    tauto,
  },
  left,
  simp only [oN₂_of_N] at ass,
  apply congr_arg,
  apply congr_arg,
  exact ass,
}) (by {
  intro r,
  rintro ⟨r_in, r_ntype⟩,
  cases List.eq_or_mem_of_mem_cons r_in with r_eq r_in_,
  {
    exfalso,
    rw r_eq at r_ntype,
    dsimp only at r_ntype,
    cases r_ntype with n₀ imposs,
    exact Option.no_confusion imposs,
  },
  cases List.eq_or_mem_of_mem_cons r_in_ with r_eq_ r_in__,
  {
    exfalso,
    rw r_eq_ at r_ntype,
    dsimp only at r_ntype,
    cases r_ntype with n₀ imposs,
    exact Option.no_confusion imposs,
  },
  clear r_in r_in_,
  rename r_in__ r_in,
  rw List.mem_append at r_in,
  cases r_in,
  {
    exfalso,
    rw List.mem_map at r_in,
    rcases r_in with ⟨r₁, r₁_in, r₁_convert_r⟩,
    rw ←r₁_convert_r at r_ntype,
    unfold rule_of_rule₁ at r_ntype,
    dsimp only at r_ntype,
    cases r_ntype with n₂ contr,
    rw Option.some_inj at contr,
    exact sum.no_confusion contr,
  },
  {
    rw List.mem_map at r_in,
    rcases r_in with ⟨r₂, r₂_in, r₂_convert_r⟩,
    use r₂,
    split,
    {
      exact r₂_in,
    },
    rw ←r₂_convert_r,
    simp only [
      lift_rule, rule_of_rule₂, lift_string, lsTN_of_lsTN₂,
      prod.mk.inj_iff, eq_self_iff_true, true_and
    ],
    five_steps,
  },
}) (by { intro, refl })

end lifted_grammars


section lemmata_subset

private lemma deri₁_more (w : List (symbol T g₁.nt)) :
  CF_derives g₁ [symbol.nonterminal g₁.initial] w →
    CF_derives
      (union_grammar g₁ g₂)
      (lsTN_of_lsTN₁ [symbol.nonterminal g₁.initial])
      (lsTN_of_lsTN₁ w) :=
begin
  intro ass,
  let gg₁ := @g₁g T g₁ g₂,
  change CF_derives gg₁.g (lsTN_of_lsTN₁ [symbol.nonterminal g₁.initial]) (lsTN_of_lsTN₁ w),
  have techni : lsTN_of_lsTN₁ = lift_string gg₁.lift_nt,
  {
    unfold lsTN_of_lsTN₁,
    unfold lift_string,
    ext1 w,
    five_steps,
  },
  rw techni,
  exact lift_deri ass,
end

private lemma deri₂_more (w : List (symbol T g₂.nt)) :
  CF_derives g₂ [symbol.nonterminal g₂.initial] w →
    CF_derives
      (union_grammar g₁ g₂)
      (lsTN_of_lsTN₂ [symbol.nonterminal g₂.initial])
      (lsTN_of_lsTN₂ w) :=
begin
  intro ass,
  let gg₂ := @g₂g T g₁ g₂,
  change CF_derives gg₂.g (lsTN_of_lsTN₂ [symbol.nonterminal g₂.initial]) (lsTN_of_lsTN₂ w),
  have techni : lsTN_of_lsTN₂ = lift_string gg₂.lift_nt,
  {
    unfold lsTN_of_lsTN₂,
    unfold lift_string,
    ext1 w,
    five_steps,
  },
  rw techni,
  exact lift_deri ass,
end

private lemma in_union_of_in_first (w : List T) :
  w ∈ CF_language g₁  →  w ∈ CF_language (union_grammar g₁ g₂)  :=
begin
  intro assum,

  have deri_start :
    CF_derives
      (union_grammar g₁ g₂)
      [symbol.nonterminal none]
      [symbol.nonterminal (some (sum.inl g₁.initial))],
  {
    apply CF_deri_of_tran,
    use (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]),
    split,
    {
      change (none, [symbol.nonterminal (some (sum.inl g₁.initial))]) ∈ (
        (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) ::
        (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) ::
        ((List.map rule_of_rule₁ g₁.rules) ++ (List.map rule_of_rule₂ g₂.rules))
      ),
      apply List.mem_cons_self,
    },
    use [[], []],
    simp,
  },

  have deri_rest :
    CF_derives
      (union_grammar g₁ g₂)
      [symbol.nonterminal (some (sum.inl g₁.initial))]
      (List.map symbol.terminal w),
  {
    have beginning :
      [symbol.nonterminal (some (sum.inl g₁.initial))] =
      lsTN_of_lsTN₁ [symbol.nonterminal g₁.initial],
    {
      unfold lsTN_of_lsTN₁,
      change
        [symbol.nonterminal (some (sum.inl g₁.initial))] =
        [sTN_of_sTN₁ (symbol.nonterminal g₁.initial)],
      unfold sTN_of_sTN₁,
    },
    have ending :
      (List.map symbol.terminal w) =
      lsTN_of_lsTN₁ (List.map symbol.terminal w),
    {
      ext1,
      unfold lsTN_of_lsTN₁,
      rw [List.nth_map, List.map_map, List.nth_map],
      apply congr_arg,
      refl,
    },
    rw beginning,
    rw ending,
    exact deri₁_more (List.map symbol.terminal w) assum,
  },

  unfold CF_language,
  rw Set.mem_SetOf_eq,
  unfold CF_generates,
  unfold CF_generates_str,
  unfold CF_derives,
  apply CF_deri_of_deri_deri deri_start,
  exact deri_rest,
end

private lemma in_union_of_in_second (w : List T) :
  w ∈ CF_language g₂  →  w ∈ CF_language (union_grammar g₁ g₂)  :=
begin
  intro assum,

  have deri_start :
    CF_derives
      (union_grammar g₁ g₂)
      [symbol.nonterminal none]
      [symbol.nonterminal (some (sum.inr g₂.initial))],
  {
    apply CF_deri_of_tran,
    use (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]),
    split,
    {
      change (none, [symbol.nonterminal (some (sum.inr g₂.initial))]) ∈ (
        (none, [symbol.nonterminal (some (sum.inl (g₁.initial)))]) ::
        (none, [symbol.nonterminal (some (sum.inr (g₂.initial)))]) ::
        ((List.map rule_of_rule₁ g₁.rules) ++ (List.map rule_of_rule₂ g₂.rules))
      ),
      apply List.mem_cons_of_mem,
      apply List.mem_cons_self,
    },
    use [[], []],
    simp,
  },

  have deri_rest :
    CF_derives
      (union_grammar g₁ g₂)
      [symbol.nonterminal (some (sum.inr g₂.initial))]
      (List.map symbol.terminal w),
  {
    have beginning :
      [symbol.nonterminal (some (sum.inr g₂.initial))] =
      lsTN_of_lsTN₂ [symbol.nonterminal g₂.initial],
    {
      unfold lsTN_of_lsTN₂,
      change
        [symbol.nonterminal (some (sum.inr g₂.initial))] =
        [sTN_of_sTN₂ (symbol.nonterminal g₂.initial)],
      unfold sTN_of_sTN₂,
    },
    have ending :
      (List.map symbol.terminal w) =
      lsTN_of_lsTN₂ (List.map symbol.terminal w),
    {
      ext1,
      unfold lsTN_of_lsTN₂,
      rw [List.nth_map, List.map_map, List.nth_map],
      apply congr_arg,
      refl,
    },
    rw beginning,
    rw ending,
    exact deri₂_more (List.map symbol.terminal w) assum,
  },

  unfold CF_language,
  rw Set.mem_SetOf_eq,
  unfold CF_generates,
  unfold CF_generates_str,
  unfold CF_derives,
  apply CF_deri_of_deri_deri deri_start,
  exact deri_rest,
end

end lemmata_subset


section lemmata_supset

meta def good_singleton : tactic unit := `[
  unfold good_string,
  intros a in_singleton,
  rw List.mem_singleton at in_singleton,
  rw in_singleton,
  unfold good_letter
]

private lemma in_language_left_case_of_union {w : List T}
    (hypo : CF_derives (union_grammar g₁ g₂)
      [symbol.nonterminal (some (sum.inl g₁.initial))]
      (List.map symbol.terminal w)) :
  w ∈ CF_language g₁ :=
begin
  unfold CF_language,
  rw Set.mem_SetOf_eq,
  unfold CF_generates,
  unfold CF_generates_str,

  let gg₁ := @g₁g T g₁ g₂,

  have bar :
    [symbol.nonterminal g₁.initial] =
    (sink_string gg₁.sink_nt [symbol.nonterminal (some (sum.inl g₁.initial))]),
  {
    unfold sink_string,
    refl,
  },
  rw bar,

  have baz : List.map symbol.terminal w = sink_string gg₁.sink_nt (List.map symbol.terminal w),
  {
    unfold sink_string,
    rw List.filter_map_map,
    change List.map symbol.terminal w = List.filter_map (λ x, (sink_symbol gg₁.sink_nt ∘ symbol.terminal) x) w,
    convert_to List.map symbol.terminal w = List.filter_map (λ x, Option.some (symbol.terminal x)) w,
    change List.map symbol.terminal w = List.filter_map (Option.some ∘ symbol.terminal) w,
    clear hypo,
    induction w with d l,
    {
      refl,
    },
    rw List.map,
    convert_to
      symbol.terminal d :: List.map symbol.terminal l =
      symbol.terminal d :: List.filter_map (some ∘ symbol.terminal) l,
    norm_num,
    exact w_ih,
  },
  rw baz,

  exact (sink_deri gg₁ [symbol.nonterminal (some (sum.inl g₁.initial))] (List.map symbol.terminal w) hypo (by {
    good_singleton,
    use g₁.initial,
    refl,
  })).left,
end

private lemma in_language_right_case_of_union {w : List T}
    (hypo : CF_derives (union_grammar g₁ g₂)
      [symbol.nonterminal (some (sum.inr g₂.initial))]
      (List.map symbol.terminal w)) :
  w ∈ CF_language g₂ :=
begin
  unfold CF_language,
  rw Set.mem_SetOf_eq,
  unfold CF_generates,
  unfold CF_generates_str,

  let gg₂ := @g₂g T g₁ g₂,

  have bar :
    [symbol.nonterminal g₂.initial] =
    (sink_string gg₂.sink_nt [symbol.nonterminal (some (sum.inr g₂.initial))]),
  {
    unfold sink_string,
    refl,
  },
  rw bar,

  have baz : List.map symbol.terminal w = sink_string gg₂.sink_nt (List.map symbol.terminal w),
  {
    unfold sink_string,
    rw List.filter_map_map,
    change List.map symbol.terminal w = List.filter_map (λ x, (sink_symbol gg₂.sink_nt ∘ symbol.terminal) x) w,
    convert_to List.map symbol.terminal w = List.filter_map (λ x, Option.some (symbol.terminal x)) w,
    change List.map symbol.terminal w = List.filter_map (Option.some ∘ symbol.terminal) w,
    clear hypo,
    induction w with d l,
    {
      refl,
    },
    rw List.map,
    convert_to
      symbol.terminal d :: List.map symbol.terminal l =
      symbol.terminal d :: List.filter_map (some ∘ symbol.terminal) l,
    norm_num,
    exact w_ih,
  },
  rw baz,

  exact (sink_deri gg₂ [symbol.nonterminal (some (sum.inr g₂.initial))] (List.map symbol.terminal w) hypo (by {
    good_singleton,
    use g₂.initial,
    refl,
  })).left,
end

private lemma both_empty
    (u v: List (symbol T (union_grammar g₁ g₂).nt))
    (a : (symbol T (union_grammar g₁ g₂).nt))
    (bef: [symbol.nonterminal (union_grammar g₁ g₂).initial] = u ++ [a] ++ v) :
  u = []  ∧  v = [] :=
begin
  have len := congr_arg List.length bef,
  rw [List.length_singleton, List.length_append, List.length_append, List.length_singleton] at len,
  split,
  {
    by_contradiction,
    rw ←List.length_eq_zero at h,
    exact Nat.not_succ_le_self 1 (by calc
      1 = (u.length + 1) + v.length : len
    ... = u.length + (1 + v.length) : add_assoc (List.length u) 1 (List.length v)
    ... ≥ 1 + (1 + v.length)        : add_le_add (Nat.one_le_iff_ne_zero.mpr h) (le_of_eq rfl)
    ... = (1 + 1) + v.length        : eq.symm (add_assoc 1 1 (List.length v))
    ... ≥ 1 + 1 + 0                 : le_self_add
    ... = 2                         : rfl),
  },
  {
    by_contradiction,
    rw ←List.length_eq_zero at h,
    exact Nat.not_succ_le_self 1 (by calc
      1 = (u.length + 1) + v.length : len
    ... ≥ (u.length + 1) + 1        : add_le_add (le_of_eq rfl) (Nat.one_le_iff_ne_zero.mpr h)
    ... = u.length + (1 + 1)        : add_assoc (List.length u) 1 1
    ... ≥ 0 + (1 + 1)               : le_add_self
    ... = (0 + 1) + 1               : eq.symm (add_assoc 0 1 1)
    ... = 2                         : rfl),
  },
end

private lemma in_language_impossible_case_of_union
    (w : List T)
    (r : (union_grammar g₁ g₂).nt × List (symbol T (union_grammar g₁ g₂).nt))
    (u v: List (symbol T (union_grammar g₁ g₂).nt))
    (hu : u = []) (hv : v = [])
    (bef: [symbol.nonterminal (union_grammar g₁ g₂).initial] = u ++ [symbol.nonterminal r.fst] ++ v)
    (sbi : r ∈ (List.map rule_of_rule₁ g₁.rules ++ List.map rule_of_rule₂ g₂.rules)) :
  w ∈ CF_language g₁ ∨ w ∈ CF_language g₂ :=
begin
  exfalso,
  rw [hu, hv] at bef,
  rw [List.nil_append, List.append_nil] at bef,
  change [symbol.nonterminal none] = [symbol.nonterminal r.fst] at bef,
  have rule_root : r.fst = none,
  {
    have almost := List.head_eq_of_cons_eq bef,
    exact symbol.nonterminal.inj almost.symm,
  },
  rw List.mem_append at sbi,
  cases sbi,
  {
    rw List.mem_map at sbi,
    rcases sbi with ⟨r₁, -, imposs⟩,
    unfold rule_of_rule₁ at imposs,
    rw ←imposs at rule_root,
    unfold prod.fst at rule_root,
    exact Option.no_confusion rule_root,
  },
  {
    rw List.mem_map at sbi,
    rcases sbi with ⟨r₂, -, imposs⟩,
    unfold rule_of_rule₂ at imposs,
    rw ←imposs at rule_root,
    unfold prod.fst at rule_root,
    exact Option.no_confusion rule_root,
  },
end

private lemma in_language_of_in_union (w : List T) :
  w ∈ CF_language (union_grammar g₁ g₂)   →   w ∈ CF_language g₁  ∨  w ∈ CF_language g₂   :=
begin
  intro ass,

  cases CF_tran_or_id_of_deri ass with impossible h,
  {
    exfalso,
    have zeroth := congr_arg (λ p, List.nth p 0) impossible,
    unfold List.nth at zeroth,
    rw List.nth_map at zeroth,
    cases (w.nth 0),
    {
      rw Option.map_none' at zeroth,
      exact Option.no_confusion zeroth,
    },
    {
      rw Option.map_some' at zeroth,
      exact symbol.no_confusion (Option.some.inj zeroth),
    },
  },
  rcases h with ⟨S₁, deri_head, deri_tail⟩,
  rcases deri_head with ⟨rule, ruleok, u, v, h_bef, h_aft⟩,

  rw h_aft at deri_tail,
  cases both_empty u v (symbol.nonterminal rule.fst) h_bef with u_nil v_nil,

  cases ruleok with g₁S r_rest,
  {
    left,
    rw g₁S at *,
    rw u_nil at deri_tail,
    rw v_nil at deri_tail,
    rw List.nil_append at deri_tail,
    exact in_language_left_case_of_union deri_tail,
  },
  cases r_rest with g₂S r_imposs,
  {
    right,
    rw g₂S at *,
    rw u_nil at deri_tail,
    rw v_nil at deri_tail,
    rw List.nil_append at deri_tail,
    exact in_language_right_case_of_union deri_tail,
  },
  exact in_language_impossible_case_of_union w rule u v u_nil v_nil h_bef r_imposs,
end

end lemmata_supset


/-- The class of context-free languages is closed under union. -/
theorem CF_of_CF_u_CF {T : Type} (L₁ : Language T) (L₂ : Language T) :
  is_CF L₁  ∧  is_CF L₂   →   is_CF (L₁ + L₂)   :=
begin
  rintro ⟨⟨g₁, eq_L₁⟩, ⟨g₂, eq_L₂⟩⟩,

  use union_grammar g₁ g₂,

  apply Set.eq_of_subSetOf_subset,
  {
    -- prove `L₁ + L₂ ⊇ `
    intros w hyp,
    rw Language.mem_add,
    rw ←eq_L₁,
    rw ←eq_L₂,
    exact in_language_of_in_union w hyp,
  },
  {
    -- prove `L₁ + L₂ ⊆ `
    intros w hyp,
    cases hyp with case₁ case₂,
    {
      rw ←eq_L₁ at case₁,
      exact in_union_of_in_first w case₁,
    },
    {
      rw ←eq_L₂ at case₂,
      exact in_union_of_in_second w case₂,
    },
  },
end
