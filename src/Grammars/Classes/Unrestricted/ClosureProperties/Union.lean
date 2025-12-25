import Grammars.Classes.Unrestricted.Basics.Lifting
import Grammars.Utilities.ListUtils


variables {T : Type}

protected def union_grammar (g₁ g₂ : grammar T) : grammar T :=
grammar.mk (Option (g₁.nt ⊕ g₂.nt)) none (
  ⟨ [], none, [], [symbol.nonterminal (some (sum.inl (g₁.initial)))] ⟩ :: (
  ⟨ [], none, [], [symbol.nonterminal (some (sum.inr (g₂.initial)))] ⟩ :: (
  (List.map (lift_rule_ (some ∘ sum.inl)) g₁.rules) ++
  (List.map (lift_rule_ (some ∘ sum.inr)) g₂.rules)
)))


variables {g₁ g₂ : grammar T}

private def oN₁_of_N : (union_grammar g₁ g₂).nt → (Option g₁.nt)
| none               := none
| (some (sum.inl n)) := some n
| (some (sum.inr _)) := none

private def oN₂_of_N : (union_grammar g₁ g₂).nt → (Option g₂.nt)
| none               := none
| (some (sum.inl _)) := none
| (some (sum.inr n)) := some n


private def lg₁ : lifted_grammar_ T :=
lifted_grammar_.mk g₁ (union_grammar g₁ g₂) (Option.some ∘ sum.inl) oN₁_of_N (by
{
  intros x y hyp,
  apply sum.inl_injective,
  apply Option.some_injective,
  exact hyp,
}
) (by
{
  intros x y hyp,
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
    rw hyp,
    right,
    refl,
  },
  cases y, swap,
  {
    tauto,
  },
  left,
  simp only [oN₁_of_N] at hyp,
  apply congr_arg,
  apply congr_arg,
  exact hyp,
}
) (by
{
  intro,
  refl,
}
) (by
{
  intros r hyp,
  apply List.mem_cons_of_mem,
  apply List.mem_cons_of_mem,
  apply List.mem_append_left,
  rw List.mem_map,
  use r,
  split,
  {
    exact hyp,
  },
  refl,
}
) (by
{
  rintros r ⟨rin, n₀, rnt⟩,
  cases rin,
  {
    exfalso,
    rw rin at rnt,
    exact Option.no_confusion rnt,
  },
  cases rin,
  {
    exfalso,
    rw rin at rnt,
    exact Option.no_confusion rnt,
  },
  change r ∈ (
      List.map (lift_rule_ (some ∘ sum.inl)) g₁.rules ++
      List.map (lift_rule_ (some ∘ sum.inr)) g₂.rules
    ) at rin,
  rw List.mem_append at rin,
  cases rin,
  {
    rw List.mem_map at rin,
    rcases rin with ⟨r₁, r₁_in, r₁_lift⟩,
    use r₁,
    split,
    {
      exact r₁_in,
    },
    exact r₁_lift,
  },
  {
    exfalso,
    rw List.mem_map at rin,
    rcases rin with ⟨r₂, r₂_in, r₂_lift⟩,
    rw ←r₂_lift at rnt,
    unfold lift_rule_ at rnt,
    dsimp only at rnt,
    have rnti := Option.some.inj rnt,
    exact sum.no_confusion rnti,
  },
})

private def lg₂ : lifted_grammar_ T :=
lifted_grammar_.mk g₂ (union_grammar g₁ g₂) (Option.some ∘ sum.inr) oN₂_of_N (by
{
  intros x y hyp,
  apply sum.inr_injective,
  apply Option.some_injective,
  exact hyp,
}
) (by
{
  intros x y hyp,
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
    rw hyp,
    refl,
  },
  cases y,
  {
    tauto,
  },
  left,
  simp only [oN₂_of_N] at hyp,
  apply congr_arg,
  apply congr_arg,
  exact hyp,
}
) (by
{
  intro,
  refl,
}
) (by
{
  intros r hyp,
  apply List.mem_cons_of_mem,
  apply List.mem_cons_of_mem,
  apply List.mem_append_right,
  rw List.mem_map,
  use r,
  split,
  {
    exact hyp,
  },
  refl,
}
) (by
{
  rintros r ⟨rin, n₀, rnt⟩,
  cases rin,
  {
    exfalso,
    rw rin at rnt,
    exact Option.no_confusion rnt,
  },
  cases rin,
  {
    exfalso,
    rw rin at rnt,
    exact Option.no_confusion rnt,
  },
  change r ∈ (
      List.map (lift_rule_ (some ∘ sum.inl)) g₁.rules ++
      List.map (lift_rule_ (some ∘ sum.inr)) g₂.rules
    ) at rin,
  rw List.mem_append at rin,
  cases rin,
  {
    exfalso,
    rw List.mem_map at rin,
    rcases rin with ⟨r₁, r₁_in, r₁_lift⟩,
    rw ←r₁_lift at rnt,
    unfold lift_rule_ at rnt,
    dsimp only at rnt,
    have rnti := Option.some.inj rnt,
    exact sum.no_confusion rnti,
  },
  {
    rw List.mem_map at rin,
    rcases rin with ⟨r₂, r₂_in, r₂_lift⟩,
    use r₂,
    split,
    {
      exact r₂_in,
    },
    exact r₂_lift,
  },
})


protected lemma in_L₁_or_L₂_of_in_union {w : List T} (ass : w ∈ grammar_language (union_grammar g₁ g₂)) :
  w ∈ grammar_language g₁  ∨  w ∈ grammar_language g₂  :=
begin
  unfold grammar_language at ass ⊢,
  rw Set.mem_SetOf_eq at ⊢ ass,
  rw Set.mem_SetOf_eq at ⊢,
  unfold grammar_generates at ass ⊢,
  have hyp := grammar_tran_or_id_of_deri ass,
  clear ass,
  cases hyp,
  {
    exfalso,
    have zeroth := congr_fun (congr_arg List.nth hyp) 0,
    cases w,
    {
      exact Option.no_confusion zeroth,
    },
    {
      rw [List.nth, List.map_cons, List.nth] at zeroth,
      have nt_eq_ter := Option.some.inj zeroth,
      exact symbol.no_confusion nt_eq_ter,
    },
  },
  rcases hyp with ⟨i, ⟨r, rin, u, v, bef, aft⟩, deri⟩,

  have uv_nil :  u = []  ∧  v = [],
  {
    have bef_len := congr_arg List.length bef,
    clear_except bef_len,
    rw List.length_singleton at bef_len,
    repeat {
      rw List.length_append at bef_len
    },
    rw List.length_singleton at bef_len,
    split;
    {
      rw ←List.length_eq_zero,
      linarith,
    },
  },
  rw [uv_nil.1, List.nil_append, uv_nil.2, List.append_nil] at bef aft,

  have same_nt : (union_grammar g₁ g₂).initial = r.input_N,
  {
    clear_except bef,
    have elemeq : [symbol.nonterminal (union_grammar g₁ g₂).initial] = [symbol.nonterminal r.input_N],
    {
      have bef_len := congr_arg List.length bef,
      rw [List.length_append_append, List.length_singleton, List.length_singleton] at bef_len,
      have rl_first : r.input_L.length = 0,
      {
        clear_except bef_len,
        linarith,
      },
      have rl_third : r.input_R.length = 0,
      {
        clear_except bef_len,
        linarith,
      },
      rw List.length_eq_zero at rl_first rl_third,
      rw [rl_first, rl_third] at bef,
      exact bef,
    },
    exact symbol.nonterminal.inj (List.head_eq_of_cons_eq elemeq),
  },

  cases rin,
  {
    rw rin at aft,
    dsimp only at aft,
    rw aft at deri,
    left,

    have sinked := sink_deri_ lg₁ deri,
    clear_except sinked,
    specialize sinked (by {
      unfold good_string_,
      simp only [List.mem_singleton, forall_eq],
      use g₁.initial,
      refl,
    }),
    convert sinked,

    unfold sink_string_,
    rw List.filter_map_map,
    convert_to List.map symbol.terminal w = List.filter_map (Option.some ∘ symbol.terminal) w,
    rw ←List.filter_map_map,
    rw List.filter_map_some,
  },
  cases rin,
  {
    rw rin at aft,
    dsimp only at aft,
    rw aft at deri,
    right,

    have sinked := sink_deri_ lg₂ deri,
    clear_except sinked,
    specialize sinked (by {
      unfold good_string_,
      simp only [List.mem_singleton, forall_eq],
      use g₂.initial,
      refl,
    }),
    convert sinked,

    unfold sink_string_,
    rw List.filter_map_map,
    convert_to List.map symbol.terminal w = List.filter_map (Option.some ∘ symbol.terminal) w,
    rw ←List.filter_map_map,
    rw List.filter_map_some,
  },
  exfalso,
  clear_except rin bef,

  change r ∈ (
      List.map (lift_rule_ (some ∘ sum.inl)) g₁.rules ++
      List.map (lift_rule_ (some ∘ sum.inr)) g₂.rules
    ) at rin,
  rw List.mem_append at rin,
  cases rin;
  rw List.mem_map at rin;
  rcases rin with ⟨ror, rri, rli⟩;
  rw ←rli at bef;
  clear_except bef,

  {
    have inb := congr_arg
      (λ z, symbol.nonterminal (lift_rule_ (Option.some ∘ sum.inl) ror).input_N ∈ z)
      bef,
    apply false_of_true_eq_false,
    convert inb.symm,
    {
      simp,
    },
    rw List.mem_singleton,
    rw symbol.nonterminal.inj_eq,
    change false = (_ = Option.none),
    unfold lift_rule_,
    clear_except,
    norm_num,
  },
  {
    have inb := congr_arg
      (λ z, symbol.nonterminal (lift_rule_ (Option.some ∘ sum.inr) ror).input_N ∈ z)
      bef,
    apply false_of_true_eq_false,
    convert inb.symm,
    {
      simp,
    },
    rw List.mem_singleton,
    rw symbol.nonterminal.inj_eq,
    change false = (_ = Option.none),
    unfold lift_rule_,
    clear_except,
    norm_num,
  },
end


protected lemma in_union_of_in_L₁ {w : List T} (ass : w ∈ grammar_language g₁) :
  w ∈ grammar_language (union_grammar g₁ g₂) :=
begin
  unfold grammar_language at ass ⊢,
  rw Set.mem_SetOf_eq at ass ⊢,
  unfold grammar_generates at ass ⊢,
  apply grammar_deri_of_tran_deri,
  {
    use ⟨ [], none, [], [symbol.nonterminal (some (sum.inl (g₁.initial)))] ⟩,
    split,
    {
      apply List.mem_cons_self,
    },
    use [[], []],
    split;
    refl,
  },
  dsimp only,
  rw [List.nil_append, List.append_nil],
  have lifted := lift_deri_ (@lg₁ _ _ g₂) ass,
  change
    grammar_derives lg₁.g
      (lift_string_ lg₁.lift_nt [symbol.nonterminal g₁.initial])
      (List.map symbol.terminal w),
  have equiv_out : (lift_string_ lg₁.lift_nt (List.map symbol.terminal w)) = (List.map symbol.terminal w),
  {
    unfold lift_string_,
    rw List.map_map,
    refl,
  },
  rw equiv_out at lifted,
  exact lifted,
end

protected lemma in_union_of_in_L₂ {w : List T} (ass : w ∈ grammar_language g₂) :
  w ∈ grammar_language (union_grammar g₁ g₂) :=
begin
  unfold grammar_language at ass ⊢,
  rw Set.mem_SetOf_eq at ass ⊢,
  unfold grammar_generates at ass ⊢,
  apply grammar_deri_of_tran_deri,
  {
    use ⟨ [], none, [], [symbol.nonterminal (some (sum.inr (g₂.initial)))] ⟩,
    split,
    {
      apply List.mem_cons_of_mem,
      apply List.mem_cons_self,
    },
    use [[], []],
    split;
    refl,
  },
  dsimp only,
  rw [List.nil_append, List.append_nil],
  have lifted := lift_deri_ (@lg₂ _ g₁ _) ass,
  change
    grammar_derives lg₂.g
      (lift_string_ lg₂.lift_nt [symbol.nonterminal g₂.initial])
      (List.map symbol.terminal w),
  have equiv_out : (lift_string_ lg₂.lift_nt (List.map symbol.terminal w)) = (List.map symbol.terminal w),
  {
    unfold lift_string_,
    rw List.map_map,
    refl,
  },
  rw equiv_out at lifted,
  exact lifted,
end


/-- The class of recursively-enumerable languages is closed under union. -/
theorem RE_of_RE_u_RE (L₁ : Language T) (L₂ : Language T) :
  is_RE L₁  ∧  is_RE L₂   →   is_RE (L₁ + L₂)   :=
begin
  rintro ⟨⟨g₁, eq_L₁⟩, ⟨g₂, eq_L₂⟩⟩,

  unfold is_RE,
  use union_grammar g₁ g₂,

  apply Set.eq_of_subSetOf_subset,
  {
    intros w ass,
    rw Language.mem_add,
    rw [←eq_L₁, ←eq_L₂],
    exact in_L₁_or_L₂_of_in_union ass,
  },
  {
    intros w ass,
    cases ass with case₁ case₂,
    {
      rw ←eq_L₁ at case₁,
      exact in_union_of_in_L₁ case₁,
    },
    {
      rw ←eq_L₂ at case₂,
      exact in_union_of_in_L₂ case₂,
    },
  },
end
