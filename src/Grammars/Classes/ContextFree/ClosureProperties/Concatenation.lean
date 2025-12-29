import Grammars.Classes.ContextFree.Basics.Lifting
import Grammars.Utilities.WrittenByOthers.TrimAssoc


variable {T : Type}

private def combined_grammar (gₗ gᵣ : CF_grammar T) : CF_grammar T :=
CF_grammar.mk
  (Option (gₗ.nt ⊕ gᵣ.nt))
  none
  ((none, [
    symbol.nonterminal (some (Sum.inl (gₗ.initial))),
    symbol.nonterminal (some (Sum.inr (gᵣ.initial)))
  ]) :: (
    (List.map rule_of_rule₁ gₗ.rules) ++ (List.map rule_of_rule₂ gᵣ.rules)
  ))

/-- similar to `sink_symbol` -/
private def oN₁_of_N {g₁ g₂ : CF_grammar T} : (combined_grammar g₁ g₂).nt → Option g₁.nt
| none => none
| (some (Sum.inl nt)) => some nt
| (some (Sum.inr _)) => none

/-- similar to `sink_symbol` -/
private def oN₂_of_N {g₁ g₂ : CF_grammar T} : (combined_grammar g₁ g₂).nt → Option g₂.nt
| none => none
| (some (Sum.inl _)) => none
| (some (Sum.inr nt)) => some nt


private def g₁g (g₁ g₂ : CF_grammar T) : @lifted_grammar T :=
lifted_grammar.mk g₁ (combined_grammar g₁ g₂) (some ∘ Sum.inl) (by
  -- prove `function.injective (some ∘ Sum.inl)` here
  intros x y hyp
  apply Sum.inl_injective
  apply Option.some_injective
  exact hyp
) (by
  -- prove `∀ r ∈ g₁.rules` we have `lift_rule (some ∘ Sum.inl) r ∈ List.map rule_of_rule₁ g₁.rules` here
  intros r hyp
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  rw [List.mem_map]
  use r
  split
  · exact hyp
  unfold rule_of_rule₁
  unfold lift_rule
  norm_num
  unfold lift_string
  unfold lsTN_of_lsTN₁
  five_steps
) oN₁_of_N (by
  intros x y ass
  cases x with
  | none =>
      right
      rfl
  | some x =>
      cases x with
      | inl =>
          cases y with
          | none =>
              rw ass
              right
              rfl
          | some y =>
              cases y with
              | inl =>
                  left
                  simp only [oN₁_of_N] at ass
                  exact congrArg (fun nt => some nt) (congrArg id ass)
              | inr =>
                  tauto
      | inr =>
          right
          rfl
) (by
  intro r
  rintro ⟨r_in, r_ntype⟩
  have r_in' := List.mem_cons.1 r_in
  cases r_in' with
  | inl r_eq =>
      exfalso
      rcases r_ntype with ⟨n₀, r_ntype⟩
      have : (some (Sum.inl n₀) : Option (g₁.nt ⊕ g₂.nt)) = none := by
        simpa [r_eq] using r_ntype
      cases this
  | inr r_in =>
      change r ∈ (List.map rule_of_rule₁ g₁.rules ++ List.map rule_of_rule₂ g₂.rules) at r_in
      rw [List.mem_append] at r_in
      cases r_in with
      | inl r_in =>
          rw [List.mem_map] at r_in
          rcases r_in with ⟨r₁, r₁_in, r₁_convert_r⟩
          use r₁
          split
          · exact r₁_in
          rw ←r₁_convert_r
          simp only [
            lift_rule, rule_of_rule₁, lift_string, lsTN_of_lsTN₁,
            prod.mk.inj_iff, eq_self_iff_true, true_and
          ]
          five_steps
      | inr r_in =>
          exfalso
          rw [List.mem_map] at r_in
          rcases r_in with ⟨r₂, r₂_in, r₂_convert_r⟩
          rcases r_ntype with ⟨n₁, r_ntype⟩
          have : (some (Sum.inl n₁) : Option (g₁.nt ⊕ g₂.nt)) =
              some (Sum.inr r₂.fst) := by
            simpa [r₂_convert_r] using r_ntype
          cases this
) (by
  intro
  rfl
)

private def g₂g (g₁ g₂ : CF_grammar T) : @lifted_grammar T :=
lifted_grammar.mk g₂ (combined_grammar g₁ g₂) (some ∘ Sum.inr) (by
  -- prove `function.injective (some ∘ Sum.inr)` here
  intros x y hyp
  apply Sum.inr_injective
  apply Option.some_injective
  exact hyp
) (by
  -- prove `∀ r ∈ g₂.rules` we have `lift_rule (some ∘ Sum.inr) r ∈ List.map rule_of_rule₂ g₂.rules` here
  intros r hyp
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  rw [List.mem_map]
  use r
  split
  · exact hyp
  unfold rule_of_rule₂
  unfold lift_rule
  norm_num
  unfold lift_string
  unfold lsTN_of_lsTN₂
  five_steps
) oN₂_of_N (by
  intros x y ass
  cases x with
  | none =>
      right
      rfl
  | some x =>
      cases x with
      | inl =>
          right
          rfl
      | inr =>
          cases y with
          | none =>
              right
              rw ass
              rfl
          | some y =>
              cases y with
              | inl =>
                  tauto
              | inr =>
                  left
                  simp only [oN₂_of_N] at ass
                  exact congrArg (fun nt => some nt) (congrArg id ass)
) (by
  intro r
  rintro ⟨r_in, r_ntype⟩
  have r_in' := List.mem_cons.1 r_in
  cases r_in' with
  | inl r_eq =>
      exfalso
      rcases r_ntype with ⟨n₀, r_ntype⟩
      have : (some (Sum.inr n₀) : Option (g₁.nt ⊕ g₂.nt)) = none := by
        simpa [r_eq] using r_ntype
      cases this
  | inr r_in =>
      change r ∈ (List.map rule_of_rule₁ g₁.rules ++ List.map rule_of_rule₂ g₂.rules) at r_in
      rw [List.mem_append] at r_in
      cases r_in with
      | inl r_in =>
          exfalso
          rw [List.mem_map] at r_in
          rcases r_in with ⟨r₁, r₁_in, r₁_convert_r⟩
          rcases r_ntype with ⟨n₂, r_ntype⟩
          have : (some (Sum.inr n₂) : Option (g₁.nt ⊕ g₂.nt)) =
              some (Sum.inl r₁.fst) := by
            simpa [r₁_convert_r] using r_ntype
          cases this
      | inr r_in =>
          rw [List.mem_map] at r_in
          rcases r_in with ⟨r₂, r₂_in, r₂_convert_r⟩
          use r₂
          split
          · exact r₂_in
          rw ←r₂_convert_r
          simp only [
            lift_rule, rule_of_rule₂, lift_string, lsTN_of_lsTN₂,
            prod.mk.inj_iff, eq_self_iff_true, true_and
          ]
          five_steps
) (by
  intro
  rfl
)


private def oT_of_sTN₃ {g₃ : CF_grammar T} : symbol T g₃.nt → Option T
| (symbol.terminal t) => some t
| (symbol.nonterminal _) => none

private def liT_of_lsTN₃ {g₃ : CF_grammar T} : List (symbol T g₃.nt) → List T :=
List.filter_map oT_of_sTN₃

private lemma u_eq_take_map_w
    {g₁ g₂ : CF_grammar T}
    (u : List (symbol T g₁.nt))
    (v : List (symbol T g₂.nt))
    (w : List T)
    (len : u.length ≤ w.length)
    (hyp : List.take u.length (List.map sTN_of_sTN₁ u ++ lsTN_of_lsTN₂ v) =
           List.take u.length (List.map symbol.terminal w)) :
  u = List.take u.length (List.map symbol.terminal w) :=
by
  ext n
  by_cases h : n < u.length
  ·
    have ass : List.map sTN_of_sTN₁ u = List.take u.length (List.map symbol.terminal w) := by
      convert hyp
      have takenl := List.take_left (List.map sTN_of_sTN₁ u) (lsTN_of_lsTN₂ v)
      rw [List.length_map] at takenl
      exact takenl.symm
    have nth_equ := congr_fun (congr_arg List.nth ass) n
    rw [List.nth_take h]
    rw [List.nth_take h] at nth_equ
    have n_lt_wl : n < w.length := by
      exact gt_of_ge_of_gt len h
    have triv : n < (List.map sTN_of_sTN₁ u).length := by
      rw [List.length_map]
      exact h
    have trig : n < (List.map (@symbol.terminal T g₁.nt) w).length := by
      rw [List.length_map]
      exact n_lt_wl
    have trin : n < (List.map (@symbol.terminal T (Option (g₁.nt ⊕ g₂.nt))) w).length := by
      rw [List.length_map]
      exact n_lt_wl
    rw [List.nthLe_nth triv] at nth_equ
    rw [List.nthLe_nth trin] at nth_equ
    rw [Option.some_inj] at nth_equ
    rw [List.nthLe_map] at nth_equ
    · exact h
    rw [List.nthLe_map] at nth_equ
    · exact n_lt_wl
    rw [List.nthLe_nth]
    · exact h
    rw [List.nthLe_nth]
    · exact trig
    apply congr_arg
    norm_num
    cases u.nthLe n h with
    | terminal =>
        unfold sTN_of_sTN₁ at nth_equ
        clear_except nth_equ
        finish
    | nonterminal =>
        exfalso
        exact symbol.no_confusion nth_equ
  ·
    have h' : u.length ≤ n := by
      exact Nat.le_of_not_lt h
    have h_u : u.nth n = none := by
      rw [List.nth_eq_none_iff]
      exact h'
    have h_rhs : (List.take u.length (List.map symbol.terminal w)).nth n = none := by
      rw [List.nth_eq_none_iff]
      rw [List.length_take]
      exact min_le_of_left_le h'
    simpa [h_u, h_rhs]

private lemma v_eq_drop_map_w
    {g₁ g₂ : CF_grammar T}
    (u : List (symbol T g₁.nt))
    (v : List (symbol T g₂.nt))
    (w : List T)
    (total_len : u.length + v.length = w.length)
    (hyp : List.drop u.length (List.map sTN_of_sTN₁ u ++ List.map sTN_of_sTN₂ v) =
           List.drop u.length (List.map symbol.terminal w)) :
  v = List.drop u.length (List.map symbol.terminal w) :=
by
  ext n
  by_cases h : n < v.length
  ·
    have nth_equ := congr_fun (congr_arg List.nth hyp) n
    rw [List.nth_drop]
    rw [List.nth_drop] at nth_equ
    rw [List.nth_drop] at nth_equ
    have hunltuv : u.length + n < u.length + v.length := by
      apply add_lt_add_left h
    have hunltw : u.length + n < w.length := by
      rw [←total_len]
      exact hunltuv
    have hlen₁ : u.length + n < (List.map sTN_of_sTN₁ u ++ List.map sTN_of_sTN₂ v).length := by
      rw [List.length_append, List.length_map, List.length_map]
      exact hunltuv
    have hlen₂ :
        u.length + n < (List.map (@symbol.terminal T (Option (g₁.nt ⊕ g₂.nt))) w).length := by
      rw [List.length_map]
      exact hunltw
    have hlen₂' : u.length + n < (List.map (@symbol.terminal T g₂.nt) w).length := by
      rw [List.length_map]
      exact hunltw
    rw [List.nthLe_nth hlen₁] at nth_equ
    rw [List.nthLe_nth hlen₂] at nth_equ
    rw [List.nthLe_nth h]
    rw [List.nthLe_nth hlen₂']
    rw [Option.some_inj] at *
    have hlen₀ : (List.map sTN_of_sTN₁ u).length ≤ u.length + n := by
      rw [List.length_map]
      exact le_self_add
    have hlen : n < (List.map (@sTN_of_sTN₂ T g₁ g₂) v).length := by
      rw [List.length_map]
      exact h
    have nth_equ_simplified :
        (List.map sTN_of_sTN₂ v).nthLe n hlen =
          (List.map symbol.terminal w).nthLe (u.length + n) hlen₂ := by
      rw [List.nthLe_append_right hlen₀] at nth_equ
      convert nth_equ
      rw [List.length_map]
      symmetry
      apply add_tsub_cancel_left
    rw [List.nthLe_map] at nth_equ_simplified
    cases v.nthLe n h with
    | terminal =>
        unfold sTN_of_sTN₂ at nth_equ_simplified
        rw [List.nthLe_map] at nth_equ_simplified
        · exact hunltw
        rw [List.nthLe_map]
        · exact hunltw
        injection nth_equ_simplified with hx
        apply congr_arg
        exact hx
    | nonterminal =>
        exfalso
        clear_except nth_equ_simplified
        finish
  ·
    have h' : v.length ≤ n := by
      exact Nat.le_of_not_lt h
    have h_v : v.nth n = none := by
      rw [List.nth_eq_none_iff]
      exact h'
    have h_rhs : (List.drop u.length (List.map symbol.terminal w)).nth n = none := by
      rw [List.nth_drop]
      rw [List.nth_eq_none_iff]
      rw [List.length_map]
      rw [←total_len]
      exact add_le_add_left h'
    simpa [h_v, h_rhs]

private def sTN₁_of_sTN {g₁ g₂ : CF_grammar T} : symbol T (Option (g₁.nt ⊕ g₂.nt)) → Option (symbol T g₁.nt)
| (symbol.terminal te) := some (symbol.terminal te)
| (symbol.nonterminal nont) := Option.map symbol.nonterminal (oN₁_of_N nont)

private def sTN₂_of_sTN {g₁ g₂ : CF_grammar T} : symbol T (Option (g₁.nt ⊕ g₂.nt)) → Option (symbol T g₂.nt)
| (symbol.terminal te) := some (symbol.terminal te)
| (symbol.nonterminal nont) := Option.map symbol.nonterminal (oN₂_of_N nont)

private def lsTN₁_of_lsTN {g₁ g₂ : CF_grammar T} (lis : List (symbol T (Option (g₁.nt ⊕ g₂.nt)))) :
  List (symbol T g₁.nt) :=
List.filter_map sTN₁_of_sTN lis

private def lsTN₂_of_lsTN {g₁ g₂ : CF_grammar T} (lis : List (symbol T (Option (g₁.nt ⊕ g₂.nt)))) :
  List (symbol T g₂.nt) :=
List.filter_map sTN₂_of_sTN lis

private lemma self_of_sTN₁ {g₁ g₂ : CF_grammar T} (a : symbol T g₁.nt) :
  sTN₁_of_sTN (@sTN_of_sTN₁ _ _ g₂ a) = a :=
by
  cases a
  rfl

private lemma self_of_sTN₂ {g₁ g₂ : CF_grammar T} (a : symbol T g₂.nt) :
  sTN₂_of_sTN (@sTN_of_sTN₂ _ g₁ _ a) = a :=
by
  cases a
  rfl

private lemma self_of_lsTN₁ {g₁ g₂ : CF_grammar T} (stri : List (symbol T g₁.nt)) :
  lsTN₁_of_lsTN (@lsTN_of_lsTN₁ _ _ g₂ stri) = stri :=
by
  unfold lsTN_of_lsTN₁
  unfold lsTN₁_of_lsTN
  rw [List.filter_map_map]
  change List.filter_map (fun x => sTN₁_of_sTN (sTN_of_sTN₁ x)) stri = stri
  convert_to List.filter_map (fun x => some x) stri = stri
  ·
    have equal_functions :
        (fun x : symbol T g₁.nt => sTN₁_of_sTN (sTN_of_sTN₁ x)) = fun x => some x := by
      ext x
      apply self_of_sTN₁
    rw [←equal_functions]
    apply congr_fun
    apply congr_arg
    ext x
    apply congr_fun
    rfl
  ·
    apply List.filter_map_some

private lemma self_of_lsTN₂ {g₁ g₂ : CF_grammar T} (stri : List (symbol T g₂.nt)) :
  lsTN₂_of_lsTN (@lsTN_of_lsTN₂ _ g₁ _ stri) = stri :=
by
  unfold lsTN_of_lsTN₂
  unfold lsTN₂_of_lsTN
  rw [List.filter_map_map]
  change List.filter_map (fun x => sTN₂_of_sTN (sTN_of_sTN₂ x)) stri = stri
  convert_to List.filter_map (fun x => some x) stri = stri
  ·
    have equal_functions :
        (fun x : symbol T g₂.nt => sTN₂_of_sTN (sTN_of_sTN₂ x)) = fun x => some x := by
      ext x
      apply self_of_sTN₂
    rw [←equal_functions]
    apply congr_fun
    apply congr_arg
    ext x
    apply congr_fun
    rfl
  ·
    apply List.filter_map_some

private lemma in_concatenated_of_in_combined
    {g₁ g₂ : CF_grammar T}
    {w : List T}
    (hyp : w ∈ CF_language (combined_grammar g₁ g₂)) :
  w ∈ CF_language g₁ * CF_language g₂ :=
begin
  rw Language.mem_mul,
  change
    CF_derives
      (combined_grammar g₁ g₂)
      [symbol.nonterminal (combined_grammar g₁ g₂).initial]
      (List.map symbol.terminal w) at hyp,

  cases CF_tran_or_id_of_deri hyp,
  {
    rename h refl_contr,
    exfalso,
    have hh := congr_fun (congr_arg List.nth refl_contr) 0,
    rw List.nth at hh,

    by_cases (List.map (@symbol.terminal T (combined_grammar g₁ g₂).nt) w).length = 0,
    {
      have empty_none : (List.map symbol.terminal w).nth 0 = none,
      {
        finish,
      },
      rw empty_none at hh,
      exact Option.no_confusion hh,
    },
    rw List.nth_map at hh,
    have hw0 : ∃ s, w.nth 0 = some s,
    {
      cases w.nth 0,
      {
        exfalso,
        exact Option.no_confusion hh,
      },
      use val,
    },
    rcases hw0 with ⟨s, hs⟩,
    rw hs at hh,
    rw Option.map_some' at hh,
    rw Option.some_inj at hh,
    exact symbol.no_confusion hh,
  },
  rcases h with ⟨y, first_step, derivation⟩,
  clear hyp,

  have only_option :
    y =
    [
      symbol.nonterminal (some (Sum.inl (g₁.initial))),
      symbol.nonterminal (some (Sum.inr (g₂.initial)))
    ],
  {
    rcases first_step with ⟨first_rule, first_rule_in, p, q, bef, aft⟩,
    have len_bef := congr_arg List.length bef,
    rw [List.length_singleton, List.length_append, List.length_append, List.length_singleton] at len_bef,
    have p_nil : p = [],
    {
      have p0 : p.length = 0,
      {
        linarith,
      },
      rw List.length_eq_zero at p0,
      exact p0,
    },
    have q_nil : q = [],
    {
      have q0 : q.length = 0,
      {
        linarith,
      },
      rw List.length_eq_zero at q0,
      exact q0,
    },
    have initial : first_rule.fst = none,
    {
      apply symbol.nonterminal.inj,
      rw p_nil at bef,
      rw q_nil at bef,
      rw List.append_nil at bef,
      rw List.nil_append at bef,
      exact List.head_eq_of_cons_eq (eq.symm bef),
    },
    have only_rule :
      first_rule = (none, [
        symbol.nonterminal (some (Sum.inl (g₁.initial))),
        symbol.nonterminal (some (Sum.inr (g₂.initial)))
      ]),
    {
      change first_rule ∈ (
        (none, [
          symbol.nonterminal (some (Sum.inl (g₁.initial))),
          symbol.nonterminal (some (Sum.inr (g₂.initial)))
        ]) :: (
          (List.map rule_of_rule₁ g₁.rules) ++ (List.map rule_of_rule₂ g₂.rules)
        )
      ) at first_rule_in,
      cases first_rule_in,
      {
        exact first_rule_in,
      },
      exfalso,
      change first_rule ∈ (List.map rule_of_rule₁ g₁.rules ++ List.map rule_of_rule₂ g₂.rules) at first_rule_in,
      rw [List.mem_append] at first_rule_in,
      cases first_rule_in,
      {
        delta rule_of_rule₁ at first_rule_in,
        have rfst :
          first_rule.fst ∈ List.map prod.fst
            (List.map (
                λ (r : g₁.nt × List (symbol T g₁.nt)),
                (some (Sum.inl r.fst), lsTN_of_lsTN₁ r.snd)
              ) g₁.rules),
        {
          exact List.mem_map_of_mem prod.fst first_rule_in,
        },
        rw initial at rfst,
        convert rfst,
        simp,
      },
      {
        delta rule_of_rule₂ at first_rule_in,
        have rfst :
          first_rule.fst ∈ List.map prod.fst
            (List.map (
                λ (r : g₂.nt × List (symbol T g₂.nt)),
                (some (Sum.inr r.fst), lsTN_of_lsTN₂ r.snd)
              ) g₂.rules),
        {
          exact List.mem_map_of_mem prod.fst first_rule_in,
        },
        rw initial at rfst,
        convert rfst,
        simp,
      },
    },
    rw [p_nil, q_nil, only_rule] at aft,
    rw List.append_nil at aft,
    rw List.nil_append at aft,
    exact aft,
  },
  clear first_step,
  rw only_option at derivation,
  clear only_option y,

  have complicated_induction :
    ∀ x : List (symbol T (combined_grammar g₁ g₂).nt),
      CF_derives
        (combined_grammar g₁ g₂)
        [
          symbol.nonterminal (some (Sum.inl (g₁.initial))),
          symbol.nonterminal (some (Sum.inr (g₂.initial)))
        ]
        x
      →
        ∃ u : List (symbol T g₁.nt), ∃ v : List (symbol T g₂.nt), and
          (CF_derives g₁ [symbol.nonterminal g₁.initial] u)
          (CF_derives g₂ [symbol.nonterminal g₂.initial] v)
          ∧ (lsTN_of_lsTN₁ u ++ lsTN_of_lsTN₂ v = x),
  {
    intros x ass,
    induction ass with a b trash orig ih,
    {
      use [[symbol.nonterminal g₁.initial], [symbol.nonterminal g₂.initial]],
      split,
      {
        split;
        apply CF_deri_self,
      },
      {
        refl,
      },
    },
    clear trash,
    rcases orig with ⟨orig_rule, orig_in, c, d, bef, aft⟩,
    rcases ih with ⟨u, v, ⟨ih₁, ih₂⟩, ih_concat⟩,
    cases orig_in,
    {
      exfalso,
      rw ←ih_concat at bef,
      rw orig_in at bef,
      clear_except bef,
      dsimp only at bef,
      have init_nt_in_bef_right : symbol.nonterminal none ∈ c ++ [symbol.nonterminal none] ++ d,
      {
        apply List.mem_append_left,
        apply List.mem_append_right,
        apply List.mem_singleton_self,
      },
      have init_nt_notin_bef_left : symbol.nonterminal none ∉ lsTN_of_lsTN₁ u ++ lsTN_of_lsTN₂ v,
      {
        rw [List.mem_append],
        push_neg,
        split,
        {
          rw List.mem_iff_nth_le,
          push_neg,
          unfold lsTN_of_lsTN₁,
          intros n hn,
          rw List.nthLe_map,
          {
            cases u.nthLe n _ with t s,
            {
              apply symbol.no_confusion,
            },
            {
              unfold sTN_of_sTN₁,
              intro hypo,
              have impossible := symbol.nonterminal.inj hypo,
              exact Option.no_confusion impossible,
            },
          },
          {
            rw List.length_map at hn,
            exact hn,
          },
        },
        {
          rw List.mem_iff_nth_le,
          push_neg,
          unfold lsTN_of_lsTN₂,
          intros n hn,
          rw List.nthLe_map,
          {
            cases v.nthLe n _ with t s,
            {
              apply symbol.no_confusion,
            },
            {
              unfold sTN_of_sTN₂,
              intro hypo,
              have impossible := symbol.nonterminal.inj hypo,
              exact Option.no_confusion impossible,
            },
          },
          {
            rw List.length_map at hn,
            exact hn,
          },
        },
      },
      rw bef at init_nt_notin_bef_left,
      exact init_nt_notin_bef_left init_nt_in_bef_right,
    },
    clear derivation w,
    change orig_rule ∈ (List.map rule_of_rule₁ g₁.rules ++ List.map rule_of_rule₂ g₂.rules) at orig_in,
    rw [List.mem_append] at orig_in,
    cases orig_in,
    {
      rw [List.mem_map] at orig_in,
      rcases orig_in with ⟨r₁, r₁_in, r₁_conv⟩,
      rw aft,
      rw bef at ih_concat,
      clear bef aft a b,
      rw ←r₁_conv at ih_concat ⊢,
      clear r₁_conv orig_rule,
      have part_for_u := congr_arg (List.take (@lsTN_of_lsTN₁ T g₁ g₂ u).length) ih_concat,
      have part_for_v := congr_arg (List.drop (@lsTN_of_lsTN₁ T g₁ g₂ u).length) ih_concat,
      rw List.take_left at part_for_u,
      rw List.drop_left at part_for_v,

      have h_len : (@lsTN_of_lsTN₁ T g₁ g₂ u).length > c.length,
      {
        by_contradiction contra,
        push_neg at contra,

        have not_in : symbol.nonterminal (rule_of_rule₁ r₁).fst ∉ lsTN_of_lsTN₂ v,
        {
          unfold lsTN_of_lsTN₂,
          rw [List.mem_map],
          rintro ⟨s, -, imposs⟩,
          cases s,
          {
            exact symbol.no_confusion imposs,
          },
          {
            have inr_eq_inl := Option.some.inj (symbol.nonterminal.inj imposs),
            exact Sum.no_confusion inr_eq_inl,
          },
        },

        have yes_in : symbol.nonterminal (@rule_of_rule₁ T g₁ g₂ r₁).fst ∈ lsTN_of_lsTN₂ v,
        {
          have lcth := congr_fun (congr_arg List.nth ih_concat) c.length,
          rw List.append_assoc c at lcth,
          have clength :
            (c ++ ([symbol.nonterminal (rule_of_rule₁ r₁).fst] ++ d)).nth c.length =
            some (symbol.nonterminal (@rule_of_rule₁ T g₁ g₂ r₁).fst),
          {
            rw List.nth_append_right, swap,
            {
              refl,
            },
            rw Nat.sub_self,
            refl,
          },
          rw clength at lcth,
          rw List.nth_append_right contra at lcth,
          exact List.nth_mem lcth,
        },

        exact not_in yes_in,
      },

      -- nonterminal was rewritten in the left half of `a` ... upgrade `u`
      let d' : List (symbol T (combined_grammar g₁ g₂).nt) :=
        List.take ((@lsTN_of_lsTN₁ T g₁ g₂ u).length - (c.length + 1)) d,
      let u' := lsTN₁_of_lsTN (c ++ (rule_of_rule₁ r₁).snd ++ d'),
      use u',
      use v,
      split,
      {
        split,
        {
          change
            CF_derives g₁ [symbol.nonterminal g₁.initial] (lsTN₁_of_lsTN (
              c ++ (rule_of_rule₁ r₁).snd ++
              (List.take ((lsTN_of_lsTN₁ u).length - (c.length + 1)) d)
            )),
          apply CF_deri_of_deri_tran ih₁,
          convert_to
            CF_transforms
              g₁
              (lsTN₁_of_lsTN (
                List.take (lsTN_of_lsTN₁ u).length (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++ d)
              ))
              (lsTN₁_of_lsTN (c ++ (rule_of_rule₁ r₁).snd ++ List.take ((lsTN_of_lsTN₁ u).length - (c.length + 1)) d)),
          {
            rw ←part_for_u,
            rw self_of_lsTN₁,
          },
          use r₁,
          split,
          {
            exact r₁_in,
          },
          use lsTN₁_of_lsTN c,
          use lsTN₁_of_lsTN (List.take (u.length - (c.length + 1)) d),
          split,
          {
            convert_to
              lsTN₁_of_lsTN (
                c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++
                  (List.take (u.length - (c.length + 1)) d)
              ) =
              lsTN₁_of_lsTN c ++ [symbol.nonterminal r₁.fst] ++
                lsTN₁_of_lsTN (List.take (u.length - (c.length + 1)) d),
            {
              apply congr_arg,
              have trivi_len : (lsTN_of_lsTN₁ u).length = u.length,
              {
                unfold lsTN_of_lsTN₁,
                rw List.length_map,
              },
              rw trivi_len,
              have another_trivi_len : c.length + 1 = (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length,
              {
                rw List.length_append,
                rw List.length_singleton,
              },
              rw another_trivi_len,

              have borrow_and_return : u.length =
                (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length +
                  (u.length - (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length),
              {
                symmetry,
                clear_except h_len,
                apply Nat.add_sub_of_le,
                rw List.length_append,
                rw List.length_singleton,
                unfold lsTN_of_lsTN₁ at h_len,
                rw List.length_map at h_len,
                rw Nat.succ_le_iff,
                exact h_len,
              },
              convert_to
                List.take
                  ((c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length +
                    (u.length - (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length))
                  (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++ d) =
                c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++
                  List.take (u.length - (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length) d,
              {
                apply congr_fun,
                apply congr_arg,
                exact borrow_and_return,
              },
              rw List.take_append,
            },
            unfold lsTN₁_of_lsTN,
            rw List.filter_map_append_append,
            refl,
          },
          {
            convert_to
              lsTN₁_of_lsTN (c ++ (rule_of_rule₁ r₁).snd ++ (List.take (u.length - (c.length + 1)) d)) =
              lsTN₁_of_lsTN c ++ r₁.snd ++ lsTN₁_of_lsTN (List.take (u.length - (c.length + 1)) d),
            {
              apply congr_arg,
              trim,
              unfold lsTN_of_lsTN₁,
              rw List.length_map,
            },
            unfold lsTN₁_of_lsTN,
            rw List.filter_map_append_append,
            change
              List.filter_map sTN₁_of_sTN c ++ lsTN₁_of_lsTN (lsTN_of_lsTN₁ r₁.snd) ++
                List.filter_map sTN₁_of_sTN (List.take (u.length - (c.length + 1)) d) =
              List.filter_map sTN₁_of_sTN c ++ r₁.snd ++
                List.filter_map sTN₁_of_sTN (List.take (u.length - (c.length + 1)) d),
            rw self_of_lsTN₁,
          },
        },
        {
          exact ih₂,
        },
      },
      {
        have trivi_min :
          min ((@lsTN_of_lsTN₁ T g₁ g₂ u).length - (c.length + 1)) d.length =
          (@lsTN_of_lsTN₁ T g₁ g₂ u).length - (c.length + 1),
        {
          apply min_eq_left,
          unfold lsTN_of_lsTN₁,
          rw List.length_map,
          clear_except part_for_u,
          unfold lsTN_of_lsTN₁ at part_for_u,
          have lengs := congr_arg List.length part_for_u,
          rw List.length_map at lengs,
          rw List.length_take at lengs,
          rw List.length_append at lengs,
          rw List.length_append at lengs,
          rw List.length_singleton at lengs,
          have uleng_le : u.length ≤ c.length + 1 + d.length,
          {
            rw ←min_eq_left_iff,
            exact lengs.symm,
          },
          clear_except uleng_le,
          omega,
        },

        have c_converted_and_back : List.map sTN_of_sTN₁ (List.filter_map sTN₁_of_sTN c) = c,
        {
          /-
            Simplified schema of this conversion (applies to some other conversions, too):
            we have `g ∘ f = id` but `f ∘ g` does not annihilate (in general)
            we need `(f ∘ g)(c) = c` for a specific `c`
            which we can express as `c = f(x)` and then
            we calculate `f(g(c)) = f(g(f(x))) = f(x) = c` hooray!
          -/
          have taken_c_from_u := congr_arg (List.take c.length) part_for_u,
          rw List.take_take at taken_c_from_u,
          rw min_eq_left (le_of_lt h_len) at taken_c_from_u,
          rw List.append_assoc at taken_c_from_u,
          rw List.take_left at taken_c_from_u,
          convert_to List.map sTN_of_sTN₁ (List.filter_map sTN₁_of_sTN (List.take c.length (lsTN_of_lsTN₁ u))) = c,
          {
            rw taken_c_from_u,
          },
          unfold lsTN_of_lsTN₁,
          rw ←List.map_take,
          change List.map sTN_of_sTN₁ (lsTN₁_of_lsTN (lsTN_of_lsTN₁ (List.take c.length u))) = _,
          rw self_of_lsTN₁,
          rw List.map_take,
          exact taken_c_from_u,
        },

        have d_converted_and_back :
          List.map sTN_of_sTN₁ (List.filter_map sTN₁_of_sTN (List.take (
            (List.map (@sTN_of_sTN₁ T g₁ g₂) u).length - (c.length + 1)
          ) d)) =
          List.take ((List.map (@sTN_of_sTN₁ T g₁ g₂) u).length - (c.length + 1)) d,
        {
          have taken_d_from_dropped_u := congr_arg (List.drop (c.length + 1)) part_for_u,
          have for_the_decomposition :
            (@lsTN_of_lsTN₁ T g₁ g₂ u).length =
            (c.length + 1) + ((@lsTN_of_lsTN₁ T g₁ g₂ u).length - (c.length + 1)),
          {
            symmetry,
            apply Nat.add_sub_of_le,
            exact Nat.succ_le_of_lt h_len,
          },
          rw for_the_decomposition at taken_d_from_dropped_u,
          rw List.drop_take at taken_d_from_dropped_u,
          have translate_counts : c.length + 1 = (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length,
          {
            rw List.length_append,
            rw List.length_singleton,
          },
          rw translate_counts at taken_d_from_dropped_u,
          rw List.drop_left at taken_d_from_dropped_u,
          rw ←translate_counts at taken_d_from_dropped_u,
          change
            List.map sTN_of_sTN₁ (
              List.filter_map sTN₁_of_sTN (List.take ((@lsTN_of_lsTN₁ T g₁ g₂ u).length - (c.length + 1)) d)
            ) = _,
          rw ←taken_d_from_dropped_u,
          change List.map sTN_of_sTN₁ (lsTN₁_of_lsTN (List.drop (c.length + 1) (List.map sTN_of_sTN₁ u))) = _,
          rw ←List.map_drop,
          change List.map sTN_of_sTN₁ (lsTN₁_of_lsTN (lsTN_of_lsTN₁ (List.drop (c.length + 1) u))) = _,
          rw self_of_lsTN₁,
          rw List.map_drop,
          exact taken_d_from_dropped_u,
        },

        have len_u' : u'.length = c.length + (@rule_of_rule₁ T g₁ g₂ r₁).snd.length + d'.length,
        {
          change
            (lsTN₁_of_lsTN (c ++ (rule_of_rule₁ r₁).snd ++ d')).length =
            c.length + (rule_of_rule₁ r₁).snd.length + d'.length,
          unfold lsTN₁_of_lsTN,
          rw List.filter_map_append_append,
          convert_to
            (List.map sTN_of_sTN₁ (
              List.filter_map sTN₁_of_sTN c ++
              List.filter_map sTN₁_of_sTN (rule_of_rule₁ r₁).snd ++
              List.filter_map sTN₁_of_sTN d'
            )).length =
            c.length + (rule_of_rule₁ r₁).snd.length + d'.length,
          {
            rw List.length_map,
          },
          rw List.map_append_append,
          rw c_converted_and_back,
          change
            (c ++ _ ++ List.map sTN_of_sTN₁ (List.filter_map sTN₁_of_sTN (
              List.take ((List.map (@sTN_of_sTN₁ T g₁ g₂) u).length - (c.length + 1)) d
            ))).length = _,
          rw d_converted_and_back,
          change (c ++ List.map sTN_of_sTN₁ (lsTN₁_of_lsTN (lsTN_of_lsTN₁ r₁.snd)) ++ d').length = _,
          rw self_of_lsTN₁,
          rw List.length_append,
          rw List.length_append,
          refl,
        },

        have express_u'_as_crd :
          lsTN_of_lsTN₁ u' =
          List.take (@lsTN_of_lsTN₁ T g₁ g₂ u').length (c ++ (rule_of_rule₁ r₁).snd ++ d),
        {
          change
            lsTN_of_lsTN₁ (lsTN₁_of_lsTN (c ++ (rule_of_rule₁ r₁).snd ++
              (List.take ((lsTN_of_lsTN₁ u).length - (c.length + 1)) d))) =
            List.take (lsTN_of_lsTN₁ u').length (c ++ (rule_of_rule₁ r₁).snd ++ d),
          convert_to
            c ++ (rule_of_rule₁ r₁).snd ++ (List.take ((lsTN_of_lsTN₁ u).length - (c.length + 1)) d) =
            List.take (lsTN_of_lsTN₁ u').length (c ++ (rule_of_rule₁ r₁).snd ++ d),
          {
            unfold lsTN₁_of_lsTN,
            rw List.filter_map_append_append,
            unfold lsTN_of_lsTN₁,
            rw List.map_append_append,
            rw c_converted_and_back,
            rw d_converted_and_back,
            change c ++ List.map sTN_of_sTN₁ (lsTN₁_of_lsTN (lsTN_of_lsTN₁ r₁.snd)) ++ _ = _,
            rw self_of_lsTN₁,
            refl,
          },

          have len_add_sub :
            (@lsTN_of_lsTN₁ T g₁ g₂ u').length =
            (c ++ (rule_of_rule₁ r₁).snd).length +
              ((@lsTN_of_lsTN₁ T g₁ g₂ u').length - (c ++ (rule_of_rule₁ r₁).snd).length),
          {
            symmetry,
            apply Nat.add_sub_of_le,
            unfold lsTN_of_lsTN₁,
            rw List.length_map,
            rw len_u',
            rw List.length_append,
            apply le_self_add,
          },
          rw len_add_sub,
          rw List.take_append,
          trim,
          rw List.length_append,
          apply congr_arg2, swap,
          {
            refl,
          },
          rw [
            lsTN_of_lsTN₁,
            List.length_map,
            List.length_map,
            len_u',
            List.length_take,
            Nat.add_sub_cancel_left,
            trivi_min,
            lsTN_of_lsTN₁,
            List.length_map
          ],
        },
        rw express_u'_as_crd,

        have identity_of_suffixes :
          List.drop (@lsTN_of_lsTN₁ T g₁ g₂ u).length (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++ d) =
          List.drop (@lsTN_of_lsTN₁ T g₁ g₂ u').length (c ++ (rule_of_rule₁ r₁).snd ++ d),
        {
          clear_except h_len trivi_min len_u',
          have h_len_ : (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length ≤ (@lsTN_of_lsTN₁ T g₁ g₂ u).length,
          {
            rw List.length_append,
            rw List.length_singleton,
            apply Nat.succ_le_of_lt,
            exact h_len,
          },
          have intermediate :
            List.drop (@lsTN_of_lsTN₁ T g₁ g₂ u).length (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++ d) =
            List.drop ((@lsTN_of_lsTN₁ T g₁ g₂ u).length - (c.length + 1)) d,
          {
            convert_to
              List.drop
                ((c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length +
                  ((lsTN_of_lsTN₁ u).length - (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length))
                (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++ d) =
              List.drop ((lsTN_of_lsTN₁ u).length - (c.length + 1)) d,
            {
              symmetry,
              apply congr_arg2, swap,
              {
                refl,
              },
              apply Nat.add_sub_of_le,
              exact h_len_,
            },
            rw List.drop_append,
            apply congr_arg2, swap,
            {
              refl,
            },
            rw List.length_append,
            rw List.length_singleton,
          },
          rw intermediate,
          change _ = List.drop (List.map sTN_of_sTN₁ u').length (c ++ (rule_of_rule₁ r₁).snd ++ d),
          rw List.length_map,
          rw len_u',
          rw ←List.length_append,
          rw List.drop_append,
          rw List.length_take,
          rw trivi_min,
        },

        rw part_for_v,
        rw identity_of_suffixes,
        apply List.take_append_drop,
      },
    },
    {
      rw [List.mem_map] at orig_in,
      rcases orig_in with ⟨r₂, r₂_in, r₂_conv⟩,
      rw aft,
      rw bef at ih_concat,
      clear bef aft a b,
      rw ←r₂_conv at ih_concat ⊢,
      clear r₂_conv orig_rule,
      have part_for_u := congr_arg (List.take (@lsTN_of_lsTN₁ T g₁ g₂ u).length) ih_concat,
      have part_for_v := congr_arg (List.drop (@lsTN_of_lsTN₁ T g₁ g₂ u).length) ih_concat,
      rw List.take_left at part_for_u,
      rw List.drop_left at part_for_v,

      have hlen_vd : (@lsTN_of_lsTN₂ T g₁ g₂ v).length > d.length,
      {
        by_contradiction contra,
        push_neg at contra,

        have not_in : symbol.nonterminal (rule_of_rule₂ r₂).fst ∉ lsTN_of_lsTN₁ u,
        {
          unfold lsTN_of_lsTN₁,
          rw [List.mem_map],
          rintro ⟨s, -, imposs⟩,
          cases s,
          {
            exact symbol.no_confusion imposs,
          },
          {
            have inl_eq_inr := Option.some.inj (symbol.nonterminal.inj imposs),
            exact Sum.no_confusion inl_eq_inr,
          },
        },

        have yes_in : symbol.nonterminal (rule_of_rule₂ r₂).fst ∈ lsTN_of_lsTN₁ u,
        {
          have ih_backwards := congr_arg List.reverse ih_concat,
          repeat {
            rw List.reverse_append at ih_backwards,
          },
          have ldth := congr_fun (congr_arg List.nth ih_backwards) d.length,
          have dlengthth :
            (d.reverse ++ ([symbol.nonterminal (rule_of_rule₂ r₂).fst].reverse ++ c.reverse)).nth d.length =
            some (symbol.nonterminal (rule_of_rule₂ r₂).fst),
          {
            rw List.nth_append_right, swap,
            {
              rw List.length_reverse,
            },
            rw List.length_reverse,
            rw Nat.sub_self,
            refl,
          },
          rw dlengthth at ldth,
          rw ←List.length_reverse at contra,
          rw List.nth_append_right contra at ldth,
          have rrr := List.nth_mem ldth,
          rw List.mem_reverse at rrr,
          exact rrr,
        },

        exact not_in yes_in,
      },
      have total_length := congr_arg List.length ih_concat,
      repeat {
        rw List.length_append at total_length,
      },
      rw List.length_singleton at total_length,
      have hlen_uc : (@lsTN_of_lsTN₁ T g₁ g₂ u).length ≤ c.length,
      {
        by_contradiction too_long,
        push_neg at too_long,
        have imposs_gt_self : c.length + 1 + d.length > c.length + 1 + d.length,
        {
          calc c.length + 1 + d.length
              = (@lsTN_of_lsTN₁ T g₁ g₂ u).length + (@lsTN_of_lsTN₂ T g₁ g₂ v).length :   total_length.symm
          ... > (@lsTN_of_lsTN₁ T g₁ g₂ u).length + d.length :   add_lt_add_left hlen_vd _
          ... ≥ c.length + d.length + 1 :   by { apply Nat.succ_le_of_lt, apply add_lt_add_right too_long, }
          ... = c.length + 1 + d.length :   Nat.add_right_comm _ _ _,
        },
        exact Nat.lt_irrefl _ imposs_gt_self,
      },
      have hlen_uc_orig : u.length ≤ c.length,
      {
        unfold lsTN_of_lsTN₁ at hlen_uc,
        rw List.length_map at hlen_uc,
        exact hlen_uc,
      },

      -- nonterminal was rewritten in the right half of `a` ... upgrade `v`
      let c' : List (symbol T (combined_grammar g₁ g₂).nt) :=
        List.drop (@lsTN_of_lsTN₁ T g₁ g₂ u).length c,
      let v' := lsTN₂_of_lsTN (c' ++ (rule_of_rule₂ r₂).snd ++ d),
      use u,
      use v',
      split,
      {
        split,
        {
          exact ih₁,
        },
        {
          change
            CF_derives g₂ [symbol.nonterminal g₂.initial] (
              @lsTN₂_of_lsTN T g₁ g₂ (List.drop (lsTN_of_lsTN₁ u).length c ++
              (rule_of_rule₂ r₂).snd ++ d)
            ),
          apply CF_deri_of_deri_tran ih₂,
          convert_to
            CF_transforms
              g₂
              (lsTN₂_of_lsTN (
                List.drop (lsTN_of_lsTN₁ u).length (c ++ [symbol.nonterminal (rule_of_rule₂ r₂).fst] ++ d)
              ))
              (lsTN₂_of_lsTN (List.drop (lsTN_of_lsTN₁ u).length c ++ (rule_of_rule₂ r₂).snd ++ d)),
          {
            rw ←part_for_v,
            rw self_of_lsTN₂,
          },
          use r₂,
          split,
          {
            exact r₂_in,
          },
          use lsTN₂_of_lsTN c',
          use lsTN₂_of_lsTN d,

          have eq_c' : List.drop u.length c = c',
          {
            change List.drop u.length c = List.drop (List.map (@sTN_of_sTN₁ T g₁ g₂) u).length c,
            rw List.length_map,
          },
          split,
          {
            unfold lsTN_of_lsTN₁,
            rw List.length_map,
            unfold lsTN₂_of_lsTN,
            rw List.append_assoc,
            rw List.drop_append_of_le_length hlen_uc_orig,
            rw ←List.append_assoc,
            rw List.filter_map_append_append,
            rw eq_c',
            refl,
          },
          {
            unfold lsTN_of_lsTN₁,
            rw List.length_map,
            unfold lsTN₂_of_lsTN,
            rw List.filter_map_append_append,
            change
              List.filter_map sTN₂_of_sTN (List.drop u.length c) ++
                lsTN₂_of_lsTN (lsTN_of_lsTN₂ r₂.snd) ++ List.filter_map sTN₂_of_sTN d =
              List.filter_map sTN₂_of_sTN c' ++ r₂.snd ++ List.filter_map sTN₂_of_sTN d,
            rw self_of_lsTN₂,
            rw eq_c',
          },
        },
      },
      {
        have identity_of_prefixes :
          List.take (@lsTN_of_lsTN₁ T g₁ g₂ u).length (c ++ [symbol.nonterminal (rule_of_rule₂ r₂).fst] ++ d) =
          List.take (@lsTN_of_lsTN₁ T g₁ g₂ u).length (c ++ (rule_of_rule₂ r₂).snd ++ d),
        {
          -- both are equal to `List.take (@lsTN_of_lsTN₁ T g₁ g₂ u).length c`
          repeat
          {
            rw List.append_assoc,
            rw List.take_append_of_le_length hlen_uc,
          },
        },

        have express_v'_as_crd :
          lsTN_of_lsTN₂ v' =
          List.drop (@lsTN_of_lsTN₁ T g₁ g₂ u).length (c ++ (rule_of_rule₂ r₂).snd ++ d),
        {
          change
            List.map sTN_of_sTN₂ (List.filter_map sTN₂_of_sTN (
              List.drop (lsTN_of_lsTN₁ u).length c ++ (rule_of_rule₂ r₂).snd ++ d)) =
            List.drop (lsTN_of_lsTN₁ u).length (c ++ (rule_of_rule₂ r₂).snd ++ d),
          rw List.filter_map_append_append,
          rw List.map_append_append,
          rw List.append_assoc c,
          rw List.drop_append_of_le_length hlen_uc,
          rw ←List.append_assoc,

          apply congr_arg2, apply congr_arg2,
          {
            have aux_plus_minus : (lsTN_of_lsTN₁ u).length + (c.length - (lsTN_of_lsTN₁ u).length) = c.length,
            {
              rw ←Nat.add_sub_assoc hlen_uc,
              rw Nat.add_sub_cancel_left,
            },
            have taken_c_from_v := congr_arg (List.take (c.length - (@lsTN_of_lsTN₁ T g₁ g₂ u).length)) part_for_v,
            rw ←List.drop_take at taken_c_from_v,
            rw List.append_assoc at taken_c_from_v,
            rw List.take_append_of_le_length (le_of_eq aux_plus_minus) at taken_c_from_v,
            rw aux_plus_minus at taken_c_from_v,
            rw List.take_length at taken_c_from_v,
            rw ←taken_c_from_v,
            unfold lsTN_of_lsTN₂,
            rw ←List.map_take,
            change
              lsTN_of_lsTN₂ (lsTN₂_of_lsTN (lsTN_of_lsTN₂ (List.take (c.length - (lsTN_of_lsTN₁ u).length) v))) =
              lsTN_of_lsTN₂ (List.take (c.length - (lsTN_of_lsTN₁ u).length) v),
            rw self_of_lsTN₂,
          },
          {
            unfold rule_of_rule₂,
            change lsTN_of_lsTN₂ (lsTN₂_of_lsTN (lsTN_of_lsTN₂ r₂.snd)) = lsTN_of_lsTN₂ r₂.snd,
            rw self_of_lsTN₂,
          },
          {
            have taken_d_from_v := congr_arg (List.drop ((@lsTN_of_lsTN₂ T g₁ g₂ v).length - d.length)) part_for_v,
            rw List.drop_drop at taken_d_from_v,
            have dropped_exactly_length :
              (@lsTN_of_lsTN₂ T g₁ g₂ v).length - d.length + (@lsTN_of_lsTN₁ T g₁ g₂ u).length =
              (c ++ [symbol.nonterminal (rule_of_rule₂ r₂).fst]).length,
            {
              rw List.length_append,
              rw List.length_singleton,
              have reorder_sum :
                (lsTN_of_lsTN₂ v).length - d.length + (lsTN_of_lsTN₁ u).length =
                (lsTN_of_lsTN₁ u).length + (lsTN_of_lsTN₂ v).length - d.length,
              {
                rw Nat.add_sub_assoc,
                apply Nat.add_comm,
                apply le_of_lt,
                exact hlen_vd,
              },
              rw reorder_sum,
              rw total_length,
              apply Nat.add_sub_cancel,
            },
            rw dropped_exactly_length at taken_d_from_v,
            rw List.drop_left at taken_d_from_v,
            rw ←taken_d_from_v,
            unfold lsTN_of_lsTN₂,
            rw ←List.map_drop,
            change
              lsTN_of_lsTN₂ (lsTN₂_of_lsTN (lsTN_of_lsTN₂ (
                List.drop ((List.map sTN_of_sTN₂ v).length - d.length) v))) =
              lsTN_of_lsTN₂ (List.drop ((List.map sTN_of_sTN₂ v).length - d.length) v),
            rw self_of_lsTN₂,
          },
        },

        rw part_for_u,
        rw identity_of_prefixes,
        rw express_v'_as_crd,
        apply List.take_append_drop,
      },
    },
  },
  specialize complicated_induction (List.map symbol.terminal w) derivation,

  rcases complicated_induction with ⟨u, v, ⟨hu, hv⟩, hw⟩,
  use liT_of_lsTN₃ u,
  use liT_of_lsTN₃ v,
  have huvw :
    @liT_of_lsTN₃ T
      (combined_grammar g₁ g₂)
      (lsTN_of_lsTN₁ u ++ lsTN_of_lsTN₂ v)
    = liT_of_lsTN₃ (List.map symbol.terminal w),
  {
    exact congr_arg liT_of_lsTN₃ hw,
  },
  split,
  {
    change CF_derives _ _ _,
    unfold liT_of_lsTN₃,
    convert hu,
    have u_from_terminals : ∃ uₜ : List T, u = List.map symbol.terminal uₜ,
    {
      unfold lsTN_of_lsTN₁ at hw,
      use List.take u.length w,
      rw List.map_take,
      exact u_eq_take_map_w u v w
        (by {
          have hwlen := congr_arg List.length hw,
          rw List.length_append at hwlen,
          rw List.length_map at hwlen,
          rw List.length_map at hwlen,
          exact Nat.le.intro hwlen,
        }) (congr_arg (List.take u.length) hw),
    },
    cases u_from_terminals with uₜ hut,
    rw hut,
    rw List.filter_map_map,
    convert_to List.map symbol.terminal (List.filter_map some uₜ) = List.map symbol.terminal uₜ,
    rw List.filter_map_some,
  },
  split,
  {
    change CF_derives _ _ _,
    unfold liT_of_lsTN₃,
    convert hv,
    have v_from_terminals : ∃ vₜ : List T, v = List.map symbol.terminal vₜ,
    {
      unfold lsTN_of_lsTN₁ at hw,
      unfold lsTN_of_lsTN₂ at hw,
      use List.drop u.length w,
      rw List.map_drop,
      have hwlen := congr_arg List.length hw,
      rw List.length_append at hwlen,
      repeat {
        rw List.length_map at hwlen,
      },
      exact v_eq_drop_map_w u v w hwlen (congr_arg (List.drop u.length) hw),
    },
    cases v_from_terminals with vₜ hvt,
    rw hvt,
    rw List.filter_map_map,
    convert_to List.map symbol.terminal (List.filter_map some vₜ) = List.map symbol.terminal vₜ,
    rw List.filter_map_some,
  },
  unfold liT_of_lsTN₃ at huvw,
  rw List.filter_map_append at huvw,
  unfold lsTN_of_lsTN₁ at huvw,
  unfold lsTN_of_lsTN₂ at huvw,
  repeat {
    rw List.filter_map_map at huvw,
  },
  have disappear_sTN_of_sTN₁ : @oT_of_sTN₃ T (combined_grammar g₁ g₂) ∘ sTN_of_sTN₁ = oT_of_sTN₃,
  {
    ext1,
    cases x;
    refl,
  },
  have disappear_sTN_of_sTN₂ : @oT_of_sTN₃ T (combined_grammar g₁ g₂) ∘ sTN_of_sTN₂ = oT_of_sTN₃,
  {
    ext1,
    cases x;
    refl,
  },
  rw disappear_sTN_of_sTN₁ at huvw,
  rw disappear_sTN_of_sTN₂ at huvw,
  unfold liT_of_lsTN₃,
  convert huvw,
  have bundle_unbundle : @oT_of_sTN₃ T (combined_grammar g₁ g₂) ∘ symbol.terminal = Option.some,
  {
    ext1,
    refl,
  },
  rw bundle_unbundle,
  rw List.filter_map_some,
end


private lemma in_combined_of_in_concatenated
    {g₁ g₂ : CF_grammar T}
    {w : List T}
    (hyp : w ∈ CF_language g₁ * CF_language g₂) :
  w ∈ CF_language (combined_grammar g₁ g₂) :=
by
  rw [Language.mem_mul] at hyp
  rcases hyp with ⟨u, v, hu, hv, hw⟩
  unfold CF_language at *
  change
    CF_derives
      (combined_grammar g₁ g₂)
      [symbol.nonterminal (combined_grammar g₁ g₂).initial]
      (List.map symbol.terminal w)

  apply @CF_deri_of_tran_deri T
    (combined_grammar g₁ g₂)
    _ [
      symbol.nonterminal (some (Sum.inl (g₁.initial))),
      symbol.nonterminal (some (Sum.inr (g₂.initial)))
    ] _
  ·
    refine ⟨(none, [
      symbol.nonterminal (some (Sum.inl (g₁.initial))),
      symbol.nonterminal (some (Sum.inr (g₂.initial)))
    ]), ?_⟩
    refine ⟨[], [], ?_⟩
    constructor
    · apply List.mem_cons_self
    constructor <;> rfl
  ·
    rw [← hw]
    rw [List.map_append]
    apply @CF_deri_of_deri_deri T
      (combined_grammar g₁ g₂) _
      (List.map symbol.terminal u ++ [symbol.nonterminal (some (Sum.inr g₂.initial))]) _
    ·
      change
        CF_derives
          (combined_grammar g₁ g₂)
          ([symbol.nonterminal (some (Sum.inl g₁.initial))] ++ [symbol.nonterminal (some (Sum.inr g₂.initial))])
          (List.map symbol.terminal u ++ [symbol.nonterminal (some (Sum.inr g₂.initial))])
      apply CF_deri_with_postfix

      change CF_derives g₁ [symbol.nonterminal g₁.initial] (List.map symbol.terminal u) at hu
      let gg₁ := g₁g g₁ g₂
      change CF_derives gg₁.g [symbol.nonterminal (some (Sum.inl g₁.initial))] (List.map symbol.terminal u)

      have ini_equ :
        [symbol.nonterminal (some (Sum.inl g₁.initial))] =
          List.map (lift_symbol gg₁.lift_nt) [symbol.nonterminal g₁.initial] := by
        apply List.singleton_eq
      rw [ini_equ]

      have baz :
          List.map symbol.terminal u =
            List.map (lift_symbol gg₁.lift_nt) (List.map symbol.terminal u) := by
        rw [List.map_map]
        apply congr_fun
        apply congr_arg
        rfl
      rw [baz]

      exact lift_deri hu
    ·
      apply CF_deri_with_prefix

      change CF_derives g₂ [symbol.nonterminal g₂.initial] (List.map symbol.terminal v) at hv
      let gg₂ := g₂g g₁ g₂
      change CF_derives gg₂.g [symbol.nonterminal (some (Sum.inr g₂.initial))] (List.map symbol.terminal v)

      have ini_equ :
        [symbol.nonterminal (some (Sum.inr g₂.initial))] =
          List.map (lift_symbol gg₂.lift_nt) [symbol.nonterminal g₂.initial] := by
        apply List.singleton_eq
      rw [ini_equ]

      have baz :
          List.map symbol.terminal v =
            List.map (lift_symbol gg₂.lift_nt) (List.map symbol.terminal v) := by
        rw [List.map_map]
        apply congr_fun
        apply congr_arg
        rfl
      rw [baz]

      exact lift_deri hv


/-- The class of context-free languages is closed under concatenation. -/
theorem CF_of_CF_c_CF (L₁ : Language T) (L₂ : Language T) :
  is_CF L₁  ∧  is_CF L₂   →   is_CF (L₁ * L₂)   :=
by
  rintro ⟨⟨g₁, eq_L₁⟩, ⟨g₂, eq_L₂⟩⟩
  refine ⟨combined_grammar g₁ g₂, ?_⟩
  apply Set.eq_of_subSetOf_subset
  ·
    -- prove `L₁ * L₂ ⊇` here
    intro w hyp
    rw [← eq_L₁, ← eq_L₂]
    exact in_concatenated_of_in_combined hyp
  ·
    -- prove `L₁ * L₂ ⊆` here
    intro w hyp
    rw [← eq_L₁] at hyp
    rw [← eq_L₂] at hyp
    exact in_combined_of_in_concatenated hyp
