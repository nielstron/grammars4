import Grammars.Classes.Unrestricted.Basics.Lifting
import Grammars.Classes.Unrestricted.ClosureProperties.Concatenation
import Grammars.Utilities.WrittenByOthers.TrimAssoc


-- new nonterminal type
private def nn (N : Type) : Type :=
N ⊕ Fin 3

-- new symbol type
private def ns (T N : Type) : Type :=
symbol T (nn N)

variables {T : Type}


section specific_symbols

private def Z {N : Type} : ns T N := symbol.nonterminal (Sum.inr 0)
private def H {N : Type} : ns T N := symbol.nonterminal (Sum.inr 1) -- denoted by `#` in the pdf
private def R {N : Type} : ns T N := symbol.nonterminal (Sum.inr 2)

private def S {g : grammar T} : ns T g.nt := symbol.nonterminal (Sum.inl g.initial)

private lemma Z_neq_H {N : Type} :  Z ≠ @H T N  :=
by
  intro ass
  have imposs : (0 : Fin 3) = 1 := by
    exact Sum.inr.inj (symbol.nonterminal.inj ass)
  exact Fin.zero_ne_one imposs

private lemma Z_neq_R {N : Type} :  Z ≠ @R T N  :=
by
  intro ass
  have imposs : (0 : Fin 3) = 2 := by
    exact Sum.inr.inj (symbol.nonterminal.inj ass)
  have zero_ne_two : (0 : Fin 3) ≠ (2 : Fin 3) := by
    decide
  exact zero_ne_two imposs

private lemma H_neq_R {N : Type} :  H ≠ @R T N  :=
by
  intro ass
  have imposs : (1 : Fin 3) = 2 := by
    exact Sum.inr.inj (symbol.nonterminal.inj ass)
  have one_ne_two : (1 : Fin 3) ≠ (2 : Fin 3) := by
    decide
  exact one_ne_two imposs

end specific_symbols


section construction

private def wrap_sym {N : Type} : symbol T N → ns T N
| (symbol.terminal t)    := symbol.terminal t
| (symbol.nonterminal n) := symbol.nonterminal (Sum.inl n)

private def wrap_gr {N : Type} (r : grule T N) : grule T (nn N) :=
grule.mk
  (List.map wrap_sym r.input_L)
  (Sum.inl r.input_N)
  (List.map wrap_sym r.input_R)
  (List.map wrap_sym r.output_string)

private def rules_that_scan_terminals (g : grammar T) : List (grule T (nn g.nt)) :=
List.map (λ t, grule.mk
    [] (Sum.inr 2) [symbol.terminal t] [symbol.terminal t, R]
  ) (all_used_terminals g)

-- based on `/informal/KleeneStar.pdf`
private def star_grammar (g : grammar T) : grammar T :=
grammar.mk (nn g.nt) (Sum.inr 0) (
  grule.mk [] (Sum.inr 0) [] [Z, S, H] ::
  grule.mk [] (Sum.inr 0) [] [R, H] ::
  grule.mk [] (Sum.inr 2) [H] [R] ::
  grule.mk [] (Sum.inr 2) [H] [] ::
  List.map wrap_gr g.rules ++
  rules_that_scan_terminals g
)

end construction


section easy_direction

private lemma short_induction {g : grammar T} {w : List (List T)}
    (ass : ∀ wᵢ ∈ w.reverse, grammar_generates g wᵢ) :
  grammar_derives (star_grammar g) [Z] (Z ::
      List.join (List.map (++ [H]) (List.map (List.map symbol.terminal) w.reverse))
    )  ∧
  ∀ p ∈ w, ∀ t ∈ p, symbol.terminal t ∈ List.join (List.map grule.output_string g.rules)  :=
begin
  induction w with v x ih,
  {
    split,
    {
      apply grammar_deri_self,
    },
    {
      intros p pin,
      exfalso,
      exact List.not_mem_nil p pin,
    },
  },
  have vx_reverse : (v :: x).reverse = x.reverse ++ [v],
  {
    apply List.reverse_cons,
  },
  rw vx_reverse at *,
  specialize ih (by {
    intros wᵢ in_reversed,
    apply ass,
    apply List.mem_append_left,
    exact in_reversed,
  }),
  specialize ass v (by {
    apply List.mem_append_right,
    apply List.mem_singleton_self,
  }),
  unfold grammar_generates at ass,
  split,
  {
    apply grammar_deri_of_tran_deri,
    {
      use (star_grammar g).rules.nthLe 0 (by dec_trivial),
      split,
      {
        apply List.nthLe_mem,
      },
      use [[], []],
      split;
      refl,
    },
    rw [List.nil_append, List.append_nil, List.map_append, List.map_append],
    change grammar_derives (star_grammar g) [Z, S, H] _,
    have ih_plus := grammar_deri_with_postfix ([S, H] : List (symbol T (star_grammar g).nt)) ih.left,
    apply grammar_deri_of_deri_deri ih_plus,
    have ass_lifted : grammar_derives (star_grammar g) [S] (List.map symbol.terminal v),
    {
      clear_except ass,
      have wrap_eq_lift : @wrap_sym T g.nt = lift_symbol_ sum.inl,
      {
        ext,
        cases x;
        refl,
      },
      let lifted_g : lifted_grammar_ T :=
        lifted_grammar_.mk g (star_grammar g) sum.inl sum.get_left (by {
          intros x y hyp,
          exact sum.inl.inj hyp,
        }) (by {
          intros x y hyp,
          cases x,
          {
            cases y,
            {
              simp only [sum.get_left] at hyp,
              left,
              congr,
              exact hyp,
            },
            {
              simp only [sum.get_left] at hyp,
              exfalso,
              exact hyp,
            },
          },
          {
            cases y,
            {
              simp only [sum.get_left] at hyp,
              exfalso,
              exact hyp,
            },
            {
              right,
              refl,
            },
          },
        }) (by {
          intro x,
          refl,
        }) (by {
          intros r rin,
          apply List.mem_cons_of_mem,
          apply List.mem_cons_of_mem,
          apply List.mem_cons_of_mem,
          apply List.mem_cons_of_mem,
          apply List.mem_append_left,
          rw List.mem_map,
          use r,
          split,
          {
            exact rin,
          },
          unfold wrap_gr,
          unfold lift_rule_,
          unfold lift_string_,
          rw wrap_eq_lift,
        }) (by {
          rintros r ⟨rin, n, nrn⟩,
          iterate 4 {
            cases rin,
            {
              exfalso,
              rw rin at nrn,
              exact sum.no_confusion nrn,
            },
          },
          change r ∈ List.map wrap_gr g.rules ++ rules_that_scan_terminals g at rin,
          rw List.mem_append at rin,
          cases rin,
          {
            clear_except rin wrap_eq_lift,
            rw List.mem_map at rin,
            rcases rin with ⟨r₀, rin₀, r_of_r₀⟩,
            use r₀,
            split,
            {
              exact rin₀,
            },
            convert r_of_r₀,
            unfold lift_rule_,
            unfold wrap_gr,
            unfold lift_string_,
            rw wrap_eq_lift,
          },
          {
            exfalso,
            unfold rules_that_scan_terminals at rin,
            rw List.mem_map at rin,
            rcases rin with ⟨t, tin, r_of_tg⟩,
            rw ←r_of_tg at nrn,
            exact sum.no_confusion nrn,
          },
        }),
      convert_to
        grammar_derives lifted_g.g
          [symbol.nonterminal (sum.inl g.initial)]
          (lift_string_ lifted_g.lift_nt (List.map symbol.terminal v)),
      {
        unfold lift_string_,
        rw List.map_map,
        congr,
      },
      exact lift_deri_ lifted_g ass,
    },
    have ass_postf := grammar_deri_with_postfix ([H] : List (symbol T (star_grammar g).nt)) ass_lifted,
    rw List.join_append,
    rw ←List.cons_append,
    apply grammar_deri_with_prefix,
    rw List.map_map,
    rw List.map_singleton,
    rw List.join_singleton,
    change grammar_derives (star_grammar g) [S, H] (List.map symbol.terminal v ++ [H]),
    convert ass_postf,
  },
  {
    intros p pin t tin,
    cases pin,
    {
      rw pin at tin,
      clear pin,
      have stin : symbol.terminal t ∈ List.map symbol.terminal v,
      {
        rw List.mem_map,
        use t,
        split,
        {
          exact tin,
        },
        {
          refl,
        },
      },
      cases grammar_generates_only_legit_terminals ass stin with rule_exists imposs,
      {
        rcases rule_exists with ⟨r, rin, stirn⟩,
        rw List.mem_join,
        use r.output_string,
        split,
        {
          rw List.mem_map,
          use r,
          split,
          {
            exact rin,
          },
          {
            refl,
          },
        },
        {
          exact stirn,
        },
      },
      {
        exfalso,
        exact symbol.no_confusion imposs,
      }
    },
    {
      exact ih.right p pin t tin,
    }
  },
end

private lemma terminal_scan_ind {g : grammar T} {w : List (List T)} (n : ℕ) (n_lt_wl : n ≤ w.length)
    (terminals : ∀ v ∈ w, ∀ t ∈ v, symbol.terminal t ∈ List.join (List.map grule.output_string g.rules)) :
  grammar_derives (star_grammar g)
    ((List.map (λ u, List.map symbol.terminal u) (List.take (w.length - n) w)).join ++ [R] ++
      (List.map (λ v, [H] ++ List.map symbol.terminal v) (List.drop (w.length - n) w)).join ++ [H])
    (List.map symbol.terminal w.join ++ [R, H])  :=
begin
  induction n with k ih,
  {
    rw Nat.sub_zero,
    rw List.drop_length,
    rw List.map_nil,
    rw List.join,
    rw List.append_nil,
    rw List.take_length,
    rw List.map_join,
    rw List.append_assoc,
    apply grammar_deri_self,
  },
  specialize ih (Nat.le_of_succ_le n_lt_wl),
  apply grammar_deri_of_deri_deri _ ih,
  clear ih,

  have wlk_succ : w.length - k = (w.length - k.succ).succ,
  {
    omega,
  },
  have lt_wl : w.length - k.succ < w.length,
  {
    omega,
  },
  have split_ldw :
    List.drop (w.length - k.succ) w =
    (w.nth (w.length - k.succ)).to_list ++ List.drop (w.length - k) w,
  {
    rw wlk_succ,
    generalize substit : w.length - k.succ = q,
    rw substit at lt_wl,
    rw ←List.take_append_drop q w,
    rw List.nth_append_right,
    swap, {
      apply List.length_take_le,
    },
    have eq_q : (List.take q w).length = q,
    {
      rw List.length_take,
      exact min_eq_left_of_lt lt_wl,
    },
    rw eq_q,
    rw Nat.sub_self,
    have drop_q_succ :
      List.drop q.succ (List.take q w ++ List.drop q w) = List.drop 1 (List.drop q w),
    {
      rw List.drop_drop,
      rw List.take_append_drop,
      rw add_comm,
    },
    rw [drop_q_succ, List.drop_left' eq_q, List.drop_drop],
    rw ←List.take_append_drop (1 + q) w,
    have q_lt : q < (List.take (1 + q) w).length,
    {
      rw List.length_take,
      exact lt_min (lt_one_add q) lt_wl,
    },
    rw List.drop_append_of_le_length (le_of_lt q_lt),
    apply congr_arg2,
    {
      rw List.nth_append,
      swap, {
        rw List.length_drop,
        exact Nat.sub_pos_of_lt q_lt,
      },
      rw List.nth_drop,
      rw add_zero,
      rw List.nth_take (lt_one_add q),
      rw add_comm,
      rw list_drop_take_succ lt_wl,
      rw List.nthLe_nth lt_wl,
      refl,
    },
    {
      rw List.take_append_drop,
    },
  },
  apply grammar_deri_with_postfix,
  rw [split_ldw, List.map_append, List.join_append, ←List.append_assoc],
  apply grammar_deri_with_postfix,
  rw [wlk_succ, List.take_succ, List.map_append, List.join_append, List.append_assoc, List.append_assoc],
  apply grammar_deri_with_prefix,
  clear_except terminals lt_wl,
  specialize terminals (w.nthLe (w.length - k.succ) lt_wl) (List.nthLe_mem w (w.length - k.succ) lt_wl),
  rw List.nthLe_nth lt_wl,
  unfold Option.to_list,
  rw [List.map_singleton, List.join_singleton, ←List.map_join, List.join_singleton],
  apply grammar_deri_of_tran_deri,
  {
    use (star_grammar g).rules.nthLe 2 (by dec_trivial),
    split_ile,
    use [[], List.map symbol.terminal (w.nthLe (w.length - k.succ) lt_wl)],
    split;
    refl,
  },
  rw List.nil_append,

  have scan_segment : ∀ m : ℕ, m ≤ (w.nthLe (w.length - k.succ) lt_wl).length →
    grammar_derives (star_grammar g)
      ([R] ++ List.map symbol.terminal (w.nthLe (w.length - k.succ) lt_wl))
      (List.map symbol.terminal (List.take m (w.nthLe (w.length - k.succ) lt_wl)) ++
        ([R] ++ List.map symbol.terminal (List.drop m (w.nthLe (w.length - k.succ) lt_wl)))),
  {
    intros m small,
    induction m with n ih,
    {
      rw ←List.append_assoc,
      convert grammar_deri_self,
    },
    apply grammar_deri_of_deri_tran (ih (Nat.le_of_succ_le small)),
    rw Nat.succ_le_iff at small,
    use ⟨[], (sum.inr 2), [symbol.terminal (List.nthLe (w.nthLe (w.length - k.succ) lt_wl) n small)],
      [symbol.terminal (List.nthLe (w.nthLe (w.length - k.succ) lt_wl) n small), R]⟩,
    split,
    {
      iterate 4 {
        apply List.mem_cons_of_mem,
      },
      apply List.mem_append_right,
      unfold rules_that_scan_terminals,
      rw List.mem_map,
      use List.nthLe (w.nthLe (w.length - k.succ) lt_wl) n small,
      split,
      {
        unfold all_used_terminals,
        rw List.mem_filter_map,
        use (w.nthLe (w.length - k.succ) lt_wl).nthLe n small,
        split,
        {
          apply terminals,
          apply List.nthLe_mem,
        },
        {
          refl,
        },
      },
      {
        refl,
      },
    },
    use List.map symbol.terminal (List.take n (w.nthLe (w.length - k.succ) lt_wl)),
    use List.map symbol.terminal (List.drop n.succ (w.nthLe (w.length - k.succ) lt_wl)),
    dsimp only,
    split,
    {
      trim,
      rw List.nil_append,
      rw List.append_assoc,
      apply congr_arg2,
      {
        refl,
      },
      rw ←List.take_append_drop 1 (List.map symbol.terminal (List.drop n (w.nthLe (w.length - k.succ) lt_wl))),
      apply congr_arg2,
      {
        rw ←List.map_take,
        rw list_take_one_drop,
        rw List.map_singleton,
      },
      {
        rw ←List.map_drop,
        rw List.drop_drop,
        rw add_comm,
      },
    },
    {
      rw List.take_succ,
      rw List.map_append,
      trim,
      rw List.nthLe_nth small,
      refl,
    },
  },
  convert scan_segment (w.nthLe (w.length - k.succ) lt_wl).length (by refl),
  {
    rw List.take_length,
  },
  {
    rw List.drop_length,
    rw List.map_nil,
    refl,
  },
end

private lemma terminal_scan_aux {g : grammar T} {w : List (List T)}
    (terminals : ∀ v ∈ w, ∀ t ∈ v, symbol.terminal t ∈ List.join (List.map grule.output_string g.rules)) :
  grammar_derives (star_grammar g)
    ([R] ++ (List.map (λ v, [H] ++ v) (List.map (List.map symbol.terminal) w)).join ++ [H])
    (List.map symbol.terminal w.join ++ [R, H])  :=
begin
  rw List.map_map,
  convert terminal_scan_ind w.length (by refl) terminals,
  {
    rw Nat.sub_self,
    rw List.take_zero,
    refl,
  },
  {
    rw Nat.sub_self,
    refl,
  },
end

end easy_direction


section hard_direction

lemma zero_of_not_ge_one {n : ℕ} (not_pos : ¬ (n ≥ 1)) :  n = 0  :=
begin
  push_neg at not_pos,
  rwa Nat.lt_one_iff at not_pos,
end

lemma length_ge_one_of_not_nil {α : Type*} {l : List α} (lnn : l ≠ []) :  l.length ≥ 1  :=
begin
  by_contradiction contra,
  have llz := zero_of_not_ge_one contra,
  rw List.length_eq_zero at llz,
  exact lnn llz,
end

private lemma nat_eq_tech {a b c : ℕ} (b_lt_c : b < c) (ass : c = a.succ + c - b.succ) :
  a = b  :=
begin
  omega,
end

private lemma wrap_never_outputs_nt_inr {N : Type} {a : symbol T N} (i : Fin 3) :
  wrap_sym a ≠ symbol.nonterminal (sum.inr i)  :=
begin
  cases a;
  unfold wrap_sym,
  {
    apply symbol.no_confusion,
  },
  intro contr,
  have inl_eq_inr := symbol.nonterminal.inj contr,
  exact sum.no_confusion inl_eq_inr,
end

private lemma wrap_never_outputs_Z {N : Type} {a : symbol T N} :
  wrap_sym a ≠ Z  :=
begin
  exact wrap_never_outputs_nt_inr 0,
end

private lemma wrap_never_outputs_H {N : Type} {a : symbol T N} :
  wrap_sym a ≠ H  :=
begin
  exact wrap_never_outputs_nt_inr 1,
end

private lemma wrap_never_outputs_R {N : Type} {a : symbol T N} :
  wrap_sym a ≠ R  :=
begin
  exact wrap_never_outputs_nt_inr 2,
end

private lemma map_wrap_never_contains_nt_inr {N : Type} {l : List (symbol T N)} (i : Fin 3) :
  symbol.nonterminal (sum.inr i) ∉ List.map wrap_sym l  :=
begin
  intro contra,
  rw List.mem_map at contra,
  rcases contra with ⟨s, -, imposs⟩,
  exact wrap_never_outputs_nt_inr i imposs,
end

private lemma map_wrap_never_contains_Z {N : Type} {l : List (symbol T N)} :
  Z ∉ List.map wrap_sym l  :=
begin
  exact map_wrap_never_contains_nt_inr 0,
end

private lemma map_wrap_never_contains_H {N : Type} {l : List (symbol T N)} :
  H ∉ List.map wrap_sym l  :=
begin
  exact map_wrap_never_contains_nt_inr 1,
end

private lemma map_wrap_never_contains_R {N : Type} {l : List (symbol T N)} :
  R ∉ List.map wrap_sym l  :=
begin
  exact map_wrap_never_contains_nt_inr 2,
end

private lemma wrap_sym_inj {N : Type} {a b : symbol T N} (wrap_eq : wrap_sym a = wrap_sym b) :
  a = b  :=
begin
  cases a,
  {
    cases b,
    {
      congr,
      exact symbol.terminal.inj wrap_eq,
    },
    {
      exfalso,
      exact symbol.no_confusion wrap_eq,
    },
  },
  {
    cases b,
    {
      exfalso,
      exact symbol.no_confusion wrap_eq,
    },
    {
      congr,
      unfold wrap_sym at wrap_eq,
      exact sum.inl.inj (symbol.nonterminal.inj wrap_eq),
    },
  },
end

private lemma wrap_str_inj {N : Type} {x y : List (symbol T N)}
    (wrap_eqs : List.map wrap_sym x = List.map wrap_sym y) :
  x = y  :=
begin
  ext1,
  have eqnth := congr_arg (λ l, List.nth l n) wrap_eqs,
  dsimp only at eqnth,
  rw List.nth_map at eqnth,
  rw List.nth_map at eqnth,

  cases x.nth n with xₙ,
  {
    cases y.nth n with yₙ,
    {
      refl,
    },
    {
      exfalso,
      exact Option.no_confusion eqnth,
    },
  },
  {
    cases y.nth n with yₙ,
    {
      exfalso,
      exact Option.no_confusion eqnth,
    },
    {
      congr,
      apply wrap_sym_inj,
      rw Option.map_some' at eqnth,
      rw Option.map_some' at eqnth,
      exact Option.some.inj eqnth,
    },
  },
end

private lemma H_not_in_rule_input {g : grammar T} {r : grule T g.nt} :
  H ∉ List.map wrap_sym r.input_L ++ [symbol.nonterminal (sum.inl r.input_N)] ++
      List.map wrap_sym r.input_R :=
begin
  intro contra,
  rw List.mem_append at contra,
  cases contra,
  swap, {
    exact map_wrap_never_contains_H contra,
  },
  rw List.mem_append at contra,
  cases contra,
  {
    exact map_wrap_never_contains_H contra,
  },
  {
    rw List.mem_singleton at contra,
    have imposs := symbol.nonterminal.inj contra,
    exact sum.no_confusion imposs,
  },
end

private lemma snsri_not_in_join_mpHmmw {g : grammar T} {x : List (List (symbol T g.nt))} {i : Fin 3}
    (snsri_neq_H : symbol.nonterminal (sum.inr i) ≠ @H T g.nt) :
  symbol.nonterminal (sum.inr i) ∉ List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x))  :=
begin
  intro contra,
  rw List.mem_join at contra,
  rw List.map_map at contra,
  rcases contra with ⟨l, l_in, in_l⟩,
  rw List.mem_map at l_in,
  rcases l_in with ⟨y, -, eq_l⟩,
  rw ←eq_l at in_l,
  rw function.comp_app at in_l,
  rw List.mem_append at in_l,
  cases in_l,
  {
    exact map_wrap_never_contains_nt_inr i in_l,
  },
  {
    rw List.mem_singleton at in_l,
    exact snsri_neq_H in_l,
  },
end

private lemma Z_not_in_join_mpHmmw {g : grammar T} {x : List (List (symbol T g.nt))} :
  Z ∉ List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x))  :=
begin
  exact snsri_not_in_join_mpHmmw Z_neq_H,
end

private lemma R_not_in_join_mpHmmw {g : grammar T} {x : List (List (symbol T g.nt))} :
  R ∉ List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x))  :=
begin
  exact snsri_not_in_join_mpHmmw H_neq_R.symm,
end

private lemma zero_Rs_in_the_long_part {g : grammar T} {x : List (List (symbol T g.nt))} [decidable_eq (ns T g.nt)] :
  List.count_in (List.map (++ [H]) (List.map (List.map wrap_sym) x)).join R = 0  :=
begin
  exact List.count_in_zero_of_notin R_not_in_join_mpHmmw,
end

private lemma cases_1_and_2_and_3a_match_aux {g : grammar T} {r₀ : grule T g.nt}
    {x : List (List (symbol T g.nt))} {u v : List (ns T g.nt)} (xnn : x ≠ [])
    (hyp : (List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x))) =
      u ++ List.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++
        List.map wrap_sym r₀.input_R ++ v) :
  ∃ m : ℕ, ∃ u₁ v₁ : List (symbol T g.nt),
    u = List.join (List.map (++ [H]) (List.take m (List.map (List.map wrap_sym) x))) ++ List.map wrap_sym u₁
    ∧  List.nth x m = some (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁)  ∧
    v = List.map wrap_sym v₁ ++ [H] ++
        List.join (List.map (++ [H]) (List.drop m.succ (List.map (List.map wrap_sym) x)))  :=
begin
  have hypp :
    (List.map (++ [H]) (List.map (List.map wrap_sym) x)).join =
    u ++ (
      List.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ List.map wrap_sym r₀.input_R
    ) ++ v,
  {
    simpa [List.append_assoc] using hyp,
  },
  have mid_brack : ∀ u', ∀ v',
    u' ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v' =
    u' ++ (r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R) ++ v',
  {
    intros,
    simp only [List.append_assoc],
  },
  simp_rw mid_brack,
  clear hyp mid_brack,

  classical,
  have count_Hs := congr_arg (λ l, List.count_in l H) hypp,
  dsimp only at count_Hs,
  rw List.count_in_append at count_Hs,
  rw List.count_in_append at count_Hs,
  rw List.count_in_zero_of_notin H_not_in_rule_input at count_Hs,
  rw add_zero at count_Hs,
  rw [List.count_in_join, List.map_map, List.map_map] at count_Hs,

  have lens := congr_arg List.length hypp,
  rw List.length_append_append at lens,
  rw List.length_append_append at lens,
  rw List.length_singleton at lens,

  have ul_lt : u.length < List.length (List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x))),
  {
    clear_except lens,
    linarith,
  },
  rcases List.take_join_of_lt ul_lt with ⟨m, k, mlt, klt, init_ul⟩,

  have vnn : v ≠ [],
  {
    by_contradiction v_nil,
    rw [v_nil, List.append_nil] at hypp,
    clear_except hypp xnn,
    have hlast := congr_arg (λ l : List (ns T g.nt), l.reverse.nth 0) hypp,
    dsimp only at hlast,
    rw [List.reverse_join, List.reverse_append, List.reverse_append_append, List.reverse_singleton] at hlast,
    have hhh : some H = ((List.map wrap_sym r₀.input_R).reverse ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ (List.map wrap_sym r₀.input_L).reverse ++ u.reverse).nth 0,
    {
      convert hlast,
      rw List.map_map,
      change some H = (List.map (λ l, List.reverse (l ++ [H])) (List.map (List.map wrap_sym) x)).reverse.join.nth 0,
      simp_rw List.reverse_append,
      rw List.map_map,
      change some H = (List.map (λ l, [H].reverse ++ (List.map wrap_sym l).reverse) x).reverse.join.nth 0,
      rw ←List.map_reverse,
      have xrnn : x.reverse ≠ [],
      {
        intro xr_nil,
        rw List.reverse_eq_iff at xr_nil,
        exact xnn xr_nil,
      },
      cases x.reverse with d l,
      {
        exfalso,
        exact xrnn rfl,
      },
      rw [List.map_cons, List.join, List.append_assoc],
      rw List.nth_append,
      swap, {
        rw List.length_reverse,
        rw List.length_singleton,
        exact one_pos,
      },
      rw List.reverse_singleton,
      refl,
    },
    rw ←List.map_reverse at hhh,
    cases r₀.input_R.reverse,
    {
      rw [List.map_nil, List.nil_append] at hhh,
      simp only [List.nth, List.cons_append] at hhh,
      exact sum.no_confusion (symbol.nonterminal.inj hhh),
    },
    {
      simp only [List.nth, List.map_cons, List.cons_append] at hhh,
      exact wrap_never_outputs_H hhh.symm,
    },
  },
  have urrrl_lt :
    List.length (u ++ (
      List.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ List.map wrap_sym r₀.input_R
    )) <
    List.length (List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x))),
  {
    have vl_pos : v.length > 0,
    {
      exact List.length_pos_of_ne_nil vnn,
    },
    clear_except lens vl_pos,
    rw List.length_append,
    rw List.length_append_append,
    rw List.length_singleton,
    linarith,
  },
  rcases List.drop_join_of_lt urrrl_lt with ⟨m', k', mlt', klt', last_vl⟩,

  have mxl : m < x.length,
  {
    rw List.length_map at mlt,
    rw List.length_map at mlt,
    exact mlt,
  },
  have mxl' : m' < x.length,
  {
    rw List.length_map at mlt',
    rw List.length_map at mlt',
    exact mlt',
  },
  have mxlmm : m < (List.map (List.map wrap_sym) x).length,
  {
    rwa List.length_map,
  },
  have mxlmm' : m' < (List.map (List.map wrap_sym) x).length,
  {
    rwa List.length_map,
  },
  use [m, List.take k (x.nthLe m mxl), List.drop k' (x.nthLe m' mxl')],

  have hyp_u := congr_arg (List.take u.length) hypp,
  rw List.append_assoc at hyp_u,
  rw List.take_left at hyp_u,
  rw init_ul at hyp_u,
  rw List.nthLe_map at hyp_u,
  swap, {
    exact mxlmm,
  },
  rw List.take_append_of_le_length at hyp_u,
  swap, {
    rw List.nthLe_map at klt,
    swap, {
      exact mxlmm,
    },
    rw List.length_append at klt,
    rw List.length_singleton at klt,
    rw List.nthLe_map at klt ⊢,
    iterate 2 {
      swap, {
        exact mxl,
      },
    },
    rw List.length_map at klt ⊢,
    rw Nat.lt_succ_iff at klt,
    exact klt,
  },
  rw ←hyp_u at count_Hs,

  have hyp_v :=
    congr_arg (List.drop (List.length (u ++ (
        List.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ List.map wrap_sym r₀.input_R
      )))) hypp,
  rw List.drop_left at hyp_v,
  rw last_vl at hyp_v,
  rw List.nthLe_map at hyp_v,
  swap, {
    exact mxlmm',
  },
  rw List.drop_append_of_le_length at hyp_v,
  swap, {
    rw List.nthLe_map at klt',
    swap, {
      exact mxlmm',
    },
    rw List.length_append at klt',
    rw List.length_singleton at klt',
    rw List.nthLe_map at klt' ⊢,
    iterate 2 {
      swap, {
        exact mxl',
      },
    },
    rw List.length_map at klt' ⊢,
    rw Nat.lt_succ_iff at klt',
    exact klt',
  },
  rw ←hyp_v at count_Hs,

  have mm : m = m',
  {
    clear_except count_Hs mxl mxl' klt klt',
    rw [
      List.count_in_append, List.count_in_append, List.map_map,
      List.count_in_join, ←List.map_take, List.map_map,
      List.count_in_join, ←List.map_drop, List.map_map
    ] at count_Hs,
    change
      (List.map (λ w, List.count_in (List.map wrap_sym w ++ [H]) H) x).sum =
      (List.map (λ w, List.count_in (List.map wrap_sym w ++ [H]) H) (List.take m x)).sum + _ +
        (_ + (List.map (λ w, List.count_in (List.map wrap_sym w ++ [H]) H) (List.drop m'.succ x)).sum)
      at count_Hs,
    simp_rw List.count_in_append at count_Hs,

    have inside_wrap : ∀ y : List (symbol T g.nt), (List.map wrap_sym y).count_in H = 0,
    {
      intro,
      rw List.count_in_zero_of_notin,
      apply map_wrap_never_contains_H,
    },
    have inside_one : ∀ z : List (symbol T g.nt),
      (List.map wrap_sym z).count_in (@H T g.nt) + [@H T g.nt].count_in (@H T g.nt) = 1,
    {
      intro,
      rw List.count_in_singleton_eq H,
      rw inside_wrap,
    },
    simp_rw inside_one at count_Hs,
    repeat {
      rw [List.map_const, List.sum_const_nat, one_mul] at count_Hs,
    },
    rw [List.length_take, List.length_drop, List.nthLe_map', List.nthLe_map'] at count_Hs,
    rw min_eq_left (le_of_lt mxl) at count_Hs,
    have inside_take : (List.take k (List.map wrap_sym (x.nthLe m mxl))).count_in H = 0,
    {
      rw ←List.map_take,
      rw inside_wrap,
    },
    have inside_drop : (List.drop k' (List.map wrap_sym (x.nthLe m' mxl'))).count_in H + [H].count_in H = 1,
    {
      rw ←List.map_drop,
      rw inside_wrap,
      rw List.count_in_singleton_eq (@H T g.nt),
    },
    rw [inside_take, inside_drop] at count_Hs,
    rw [add_zero, ←add_assoc, ←Nat.add_sub_assoc] at count_Hs,
    swap, {
      rwa Nat.succ_le_iff,
    },
    exact nat_eq_tech mxl' count_Hs,
  },
  rw ←mm at *,

  split,
  {
    symmetry,
    convert hyp_u,
    {
      rw List.map_take,
    },
    {
      rw List.map_take,
      rw List.nthLe_map,
    },
  },
  split,
  swap, {
    symmetry,
    convert hyp_v,
    {
      rw List.map_drop,
      rw List.nthLe_map,
    },
    {
      rw List.map_drop,
      rw mm,
    },
  },
  rw [←hyp_u, ←hyp_v] at hypp,

  have mltx : m < x.length,
  {
    rw List.length_map at mlt,
    rw List.length_map at mlt,
    exact mlt,
  },
  have xxx : x = x.take m ++ [x.nthLe m mltx] ++ x.drop m.succ,
  {
    rw List.append_assoc,
    rw List.singleton_append,
    rw List.cons_nth_le_drop_succ,
    rw List.take_append_drop,
  },
  have hyppp :
    (List.map (++ [H]) (List.map (List.map wrap_sym) (x.take m ++ [x.nthLe m mltx] ++ x.drop m.succ))).join =
    (List.take m (List.map (++ [H]) (List.map (List.map wrap_sym) x))).join ++
      List.take k ((List.map (List.map wrap_sym) x).nthLe m mxlmm) ++
      (List.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ List.map wrap_sym r₀.input_R) ++
      (List.drop k' ((List.map (List.map wrap_sym) x).nthLe m mxlmm) ++ [H] ++
      (List.drop m.succ (List.map (++ [H]) (List.map (List.map wrap_sym) x))).join),
  {
    convert hypp,
    exact xxx.symm,
  },
  clear_except hyppp mm,
  rw [
    List.map_append_append, List.map_append_append,
    List.join_append_append,
    List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    List.map_take, List.map_take,
    List.append_right_inj,
    ←List.append_assoc, ←List.append_assoc, ←List.append_assoc, ←List.append_assoc, ←List.append_assoc,
    List.map_drop, List.map_drop,
    List.append_left_inj,
    List.map_singleton, List.map_singleton, List.join_singleton,
    List.append_left_inj
  ] at hyppp,
  rw List.nthLe_nth mltx,
  apply congr_arg,
  apply wrap_str_inj,
  rw hyppp,
  rw List.map_append_append,
  rw List.map_take,
  rw List.nthLe_map,
  swap, {
    exact mltx,
  },
  rw List.map_drop,
  rw List.map_append_append,
  rw List.map_singleton,
  rw ←List.append_assoc,
  rw ←List.append_assoc,
  apply congr_arg2,
  {
    refl,
  },
  congr,
  exact mm,
end

private lemma case_1_match_rule {g : grammar T} {r₀ : grule T g.nt}
    {x : List (List (symbol T g.nt))} {u v : List (ns T g.nt)}
    (hyp : Z :: (List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x))) =
      u ++ List.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++
        List.map wrap_sym r₀.input_R ++ v) :
  ∃ m : ℕ, ∃ u₁ v₁ : List (symbol T g.nt),
    u = Z :: List.join (List.map (++ [H]) (List.take m (List.map (List.map wrap_sym) x))) ++ List.map wrap_sym u₁
    ∧  List.nth x m = some (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁)  ∧
    v = List.map wrap_sym v₁ ++ [H] ++
        List.join (List.map (++ [H]) (List.drop m.succ (List.map (List.map wrap_sym) x)))  :=
begin
  by_cases is_x_nil : x = [],
  {
    exfalso,
    rw [is_x_nil, List.map_nil, List.map_nil, List.join] at hyp,
    have hyp_len := congr_arg List.length hyp,
    rw List.length_singleton at hyp_len,
    repeat {
      rw List.length_append at hyp_len,
    },
    rw List.length_singleton at hyp_len,
    have left_nil : u ++ List.map wrap_sym r₀.input_L = [],
    {
      rw ←List.length_eq_zero,
      rw List.length_append,
      omega,
    },
    have right_nil : List.map wrap_sym r₀.input_R ++ v = [],
    {
      rw ←List.length_eq_zero,
      rw List.length_append,
      omega,
    },
    rw [left_nil, List.nil_append, List.append_assoc, right_nil, List.append_nil] at hyp,
    have imposs := List.head_eq_of_cons_eq hyp,
    unfold Z at imposs,
    rw symbol.nonterminal.inj_eq at imposs,
    exact sum.no_confusion imposs,
  },
  have unn : u ≠ [],
  {
    by_contradiction u_nil,
    rw [u_nil, List.nil_append] at hyp,
    cases r₀.input_L with d l,
    {
      rw [List.map_nil, List.nil_append] at hyp,
      have imposs := List.head_eq_of_cons_eq hyp,
      have inr_eq_inl := symbol.nonterminal.inj imposs,
      exact sum.no_confusion inr_eq_inl,
    },
    {
      rw List.map_cons at hyp,
      have imposs := List.head_eq_of_cons_eq hyp,
      cases d,
      {
        unfold wrap_sym at imposs,
        exact symbol.no_confusion imposs,
      },
      {
        unfold wrap_sym at imposs,
        have inr_eq_inl := symbol.nonterminal.inj imposs,
        exact sum.no_confusion inr_eq_inl,
      },
    },
  },
  have hypr := congr_arg List.tail hyp,
  rw List.tail at hypr,
  repeat {
    rw List.append_assoc at hypr,
  },
  rw List.tail_append_of_ne_nil _ _ unn at hypr,
  repeat {
    rw ←List.append_assoc at hypr,
  },
  rcases cases_1_and_2_and_3a_match_aux is_x_nil hypr with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩,
  use [m, u₁, v₁],
  split,
  {
    cases u with d l,
    {
      exfalso,
      exact unn rfl,
    },
    have headZ : d = Z,
    {
      repeat {
        rw List.cons_append at hyp,
      },
      exact List.head_eq_of_cons_eq hyp.symm,
    },
    rw headZ,
    rw List.tail at u_eq,
    rw u_eq,
    apply List.cons_append,
  },
  split,
  {
    exact xm_eq,
  },
  {
    exact v_eq,
  },
end

private lemma star_case_1 {g : grammar T} {α α' : List (ns T g.nt)}
    (orig : grammar_transforms (star_grammar g) α α')
    (hyp : ∃ x : List (List (symbol T g.nt)),
      (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
      (α = [Z] ++ List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x)))) :
  (∃ x : List (List (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = [Z] ++ List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x))))  ∨
  (∃ x : List (List (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = [R, H] ++ List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x))))  :=
begin
  rcases hyp with ⟨x, valid, cat⟩,
  have no_R_in_alpha : R ∉ α,
  {
    intro contr,
    rw cat at contr,
    clear_except contr,
    rw List.mem_append at contr,
    cases contr,
    {
      rw List.mem_singleton at contr,
      exact Z_neq_R.symm contr,
    },
    {
      exact R_not_in_join_mpHmmw contr,
    },
  },
  rw cat at *,
  clear cat,
  rcases orig with ⟨r, rin, u, v, bef, aft⟩,

  cases rin,
  {
    left,
    rw rin at *,
    clear rin,
    dsimp only at *,
    rw [List.append_nil, List.append_nil] at bef,
    use ([symbol.nonterminal g.initial] :: x),
    split,
    {
      intros xᵢ xin,
      cases xin,
      {
        rw xin,
        apply grammar_deri_self,
      },
      {
        exact valid xᵢ xin,
      },
    },
    have u_nil : u = [],
    {
      clear_except bef,
      rw ←List.length_eq_zero,
      by_contradiction,
      have ul_pos : 0 < u.length,
      {
        rwa pos_iff_ne_zero,
      },
      clear h,
      have bef_tail := congr_arg List.tail bef,
      cases u with d l,
      {
        rw List.length at ul_pos,
        exact Nat.lt_irrefl 0 ul_pos,
      },
      {
        have Z_in_tail : Z ∈ l ++ [symbol.nonterminal (sum.inr 0)] ++ v,
        {
          apply List.mem_append_left,
          apply List.mem_append_right,
          apply List.mem_singleton_self,
        },
        rw [List.singleton_append, List.tail_cons, List.cons_append, List.cons_append, List.tail_cons] at bef_tail,
        rw ←bef_tail at Z_in_tail,
        exact Z_not_in_join_mpHmmw Z_in_tail,
      },
    },
    have v_rest : v = List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x)),
    {
      rw u_nil at bef,
      convert congr_arg List.tail bef.symm,
    },
    rw aft,
    rw [u_nil, v_rest],
    rw [List.nil_append, List.map_cons],
    refl,
  },
  cases rin,
  {
    right,
    rw rin at *,
    clear rin,
    dsimp only at *,
    rw [List.append_nil, List.append_nil] at bef,
    use x,
    split,
    {
      exact valid,
    },
    have u_nil : u = [],
    {
      clear_except bef,
      rw ←List.length_eq_zero,
      by_contradiction,
      have ul_pos : 0 < u.length,
      {
        rwa pos_iff_ne_zero,
      },
      clear h,
      have bef_tail := congr_arg List.tail bef,
      cases u with d l,
      {
        rw List.length at ul_pos,
        exact Nat.lt_irrefl 0 ul_pos,
      },
      {
        have Z_in_tail : Z ∈ l ++ [symbol.nonterminal (sum.inr 0)] ++ v,
        {
          apply List.mem_append_left,
          apply List.mem_append_right,
          apply List.mem_singleton_self,
        },
        rw [List.singleton_append, List.tail_cons, List.cons_append, List.cons_append, List.tail_cons] at bef_tail,
        rw ←bef_tail at Z_in_tail,
        exact Z_not_in_join_mpHmmw Z_in_tail,
      },
    },
    have v_rest : v = List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x)),
    {
      rw u_nil at bef,
      convert congr_arg List.tail bef.symm,
    },
    rw aft,
    rw [u_nil, v_rest],
    refl,
  },
  iterate 2 {
    cases rin,
    {
      exfalso,
      apply no_R_in_alpha,
      rw bef,
      apply List.mem_append_left,
      apply List.mem_append_left,
      apply List.mem_append_right,
      rw List.mem_singleton,
      rw rin,
      refl,
    },
  },
  have rin' : r ∈ rules_that_scan_terminals g ∨ r ∈ List.map wrap_gr g.rules,
  {
    rw or_comm,
    rwa ←List.mem_append,
  },
  clear rin,
  cases rin',
  {
    exfalso,
    apply no_R_in_alpha,
    rw bef,
    apply List.mem_append_left,
    apply List.mem_append_left,
    apply List.mem_append_right,
    rw List.mem_singleton,
    unfold rules_that_scan_terminals at rin',
    rw List.mem_map at rin',
    rcases rin' with ⟨t, -, form⟩,
    rw ←form,
    refl,
  },
  left,
  rw List.mem_map at rin',
  rcases rin' with ⟨r₀, orig_in, wrap_orig⟩,
  unfold wrap_gr at wrap_orig,
  rw ←wrap_orig at *,
  clear wrap_orig,
  dsimp only at *,
  rcases case_1_match_rule bef with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩,
  clear bef,
  rw [u_eq, v_eq] at aft,
  use (List.take m x ++ [u₁ ++ r₀.output_string ++ v₁] ++ List.drop m.succ x),
  split,
  {
    intros xᵢ xiin,
    rw List.mem_append_append at xiin,
    cases xiin,
    {
      apply valid,
      exact List.mem_of_mem_take xiin,
    },
    cases xiin,
    swap, {
      apply valid,
      exact List.mem_of_mem_drop xiin,
    },
    rw List.mem_singleton at xiin,
    rw xiin,
    have last_step :
      grammar_transforms g
        (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁)
        (u₁ ++ r₀.output_string ++ v₁),
    {
      use r₀,
      split,
      {
        exact orig_in,
      },
      use [u₁, v₁],
      split;
      refl,
    },
    apply grammar_deri_of_deri_tran _ last_step,
    apply valid (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁),
    exact List.nth_mem xm_eq,
  },
  rw List.singleton_append,
  rw aft,
  repeat {
    rw List.cons_append,
  },
  apply congr_arg2,
  {
    refl,
  },
  repeat {
    rw List.map_append,
  },
  rw List.join_append_append,
  repeat {
    rw List.append_assoc,
  },
  apply congr_arg2,
  {
    rw ←List.map_take,
  },
  repeat {
    rw ←List.append_assoc,
  },
  apply congr_arg2,
  swap, {
    rw ←List.map_drop,
  },
  rw [
    List.map_singleton, List.map_singleton, List.join_singleton,
    List.map_append, List.map_append
  ],
end

private lemma uv_nil_of_RH_eq {g : grammar T} {u v : List (ns T g.nt)}
    (ass : [R, H] = u ++ [] ++ [symbol.nonterminal (sum.inr 2)] ++ [H] ++ v) :
  u = []  ∧  v = []  :=
begin
  rw List.append_nil at ass,
  have lens := congr_arg List.length ass,
  simp only [List.length_append, List.length, zero_add] at lens,
  split;
  {
    rw ←List.length_eq_zero,
    omega,
  },
end

private lemma u_nil_when_RH {g : grammar T} {x : List (List (symbol T g.nt))} {u v : List (ns T g.nt)}
    (ass :
      [R, H] ++ (List.map (++ [H]) (List.map (List.map wrap_sym) x)).join =
      u ++ [] ++ [symbol.nonterminal (sum.inr 2)] ++ [H] ++ v
    ) :
  u = []  :=
begin
  cases u with d l,
  {
    refl,
  },
  rw List.append_nil at ass,
  exfalso,
  by_cases d = R,
  {
    rw h at ass,
    clear h,
    classical,
    have imposs, { dsimp_result { exact congr_arg (λ c : List (ns T g.nt), List.count_in c R) ass } },
    repeat {
      rw List.count_in_append at imposs,
    },
    repeat {
      rw List.count_in_cons at imposs,
    },
    repeat {
      rw List.count_in_nil at imposs,
    },
    have one_imposs : 1 + (0 + 0) + 0 = 1 + List.count_in l R + (1 + 0) + (0 + 0) + List.count_in v R,
    {
      convert imposs,
      {
        norm_num,
      },
      {
        simp [H_neq_R],
      },
      {
        symmetry,
        apply zero_Rs_in_the_long_part,
      },
      {
        norm_num,
      },
      {
        simp [R],
      },
      {
        simp [H_neq_R],
      },
    },
    clear_except one_imposs,
    repeat {
      rw add_zero at one_imposs,
    },
    linarith,
  },
  {
    apply h,
    clear h,
    have impos := congr_fun (congr_arg List.nth ass) 0,
    iterate 4 {
      rw List.nth_append at impos,
      swap, {
        norm_num,
      },
    },
    rw List.nth at impos,
    rw List.nth at impos,
    exact (Option.some.inj impos).symm,
  },
end

private lemma case_2_match_rule {g : grammar T} {r₀ : grule T g.nt}
    {x : List (List (symbol T g.nt))} {u v : List (ns T g.nt)}
    (hyp : R :: H :: (List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x))) =
      u ++ List.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++
        List.map wrap_sym r₀.input_R ++ v) :
  ∃ m : ℕ, ∃ u₁ v₁ : List (symbol T g.nt),
    u = R :: H :: List.join (List.map (++ [H]) (List.take m (List.map (List.map wrap_sym) x))) ++ List.map wrap_sym u₁
    ∧  List.nth x m = some (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁)  ∧
    v = List.map wrap_sym v₁ ++ [H] ++
        List.join (List.map (++ [H]) (List.drop m.succ (List.map (List.map wrap_sym) x)))  :=
begin
  by_cases is_x_nil : x = [],
  {
    exfalso,
    rw [is_x_nil, List.map_nil, List.map_nil, List.join] at hyp,
    have imposs : symbol.nonterminal (sum.inl r₀.input_N) = R ∨ symbol.nonterminal (sum.inl r₀.input_N) = H,
    {
      simpa using congr_arg (λ l, symbol.nonterminal (sum.inl r₀.input_N) ∈ l) hyp,
    },
    cases imposs;
    exact sum.no_confusion (symbol.nonterminal.inj imposs),
  },
  have unn : u ≠ [],
  {
    by_contradiction u_nil,
    rw [u_nil, List.nil_append] at hyp,
    cases r₀.input_L with d l,
    {
      rw [List.map_nil, List.nil_append] at hyp,
      have imposs := List.head_eq_of_cons_eq hyp,
      have inr_eq_inl := symbol.nonterminal.inj imposs,
      exact sum.no_confusion inr_eq_inl,
    },
    {
      rw List.map_cons at hyp,
      have imposs := List.head_eq_of_cons_eq hyp,
      cases d,
      {
        unfold wrap_sym at imposs,
        exact symbol.no_confusion imposs,
      },
      {
        unfold wrap_sym at imposs,
        have inr_eq_inl := symbol.nonterminal.inj imposs,
        exact sum.no_confusion inr_eq_inl,
      },
    },
  },
  have hypt := congr_arg List.tail hyp,
  rw List.tail at hypt,
  repeat {
    rw List.append_assoc at hypt,
  },
  rw List.tail_append_of_ne_nil _ _ unn at hypt,
  have utnn : u.tail ≠ [],
  {
    by_contradiction ut_nil,
    rw [ut_nil, List.nil_append] at hypt,
    cases r₀.input_L with d l,
    {
      rw [List.map_nil, List.nil_append] at hypt,
      have imposs := List.head_eq_of_cons_eq hypt,
      have inr_eq_inl := symbol.nonterminal.inj imposs,
      exact sum.no_confusion inr_eq_inl,
    },
    {
      rw List.map_cons at hypt,
      have imposs := List.head_eq_of_cons_eq hypt,
      cases d,
      {
        unfold wrap_sym at imposs,
        exact symbol.no_confusion imposs,
      },
      {
        unfold wrap_sym at imposs,
        have inr_eq_inl := symbol.nonterminal.inj imposs,
        exact sum.no_confusion inr_eq_inl,
      },
    },
  },
  have hyptt := congr_arg List.tail hypt,
  rw List.tail at hyptt,
  rw List.tail_append_of_ne_nil _ _ utnn at hyptt,
  repeat {
    rw ←List.append_assoc at hyptt,
  },
  rcases cases_1_and_2_and_3a_match_aux is_x_nil hyptt with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩,
  use [m, u₁, v₁],
  split,
  {
    cases u with d l,
    {
      exfalso,
      exact unn rfl,
    },
    have headR : d = R,
    {
      repeat {
        rw List.cons_append at hyp,
      },
      exact List.head_eq_of_cons_eq hyp.symm,
    },
    rw List.tail at u_eq,
    rw List.tail at hypt,
    cases l with d' l',
    {
      exfalso,
      exact utnn rfl,
    },
    have tailHead : d' = H,
    {
      repeat {
        rw List.cons_append at hypt,
      },
      exact List.head_eq_of_cons_eq hypt.symm,
    },
    rw List.tail at u_eq,
    rw [headR, tailHead, u_eq, List.cons_append, List.cons_append],
  },
  split,
  {
    exact xm_eq,
  },
  {
    exact v_eq,
  },
end

private lemma star_case_2 {g : grammar T} {α α' : List (symbol T (star_grammar g).nt)}
    (orig : grammar_transforms (star_grammar g) α α')
    (hyp : ∃ x : List (List (symbol T g.nt)),
      (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
      (α = [R, H] ++ List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x)))) :
  (∃ x : List (List (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = [R, H] ++ List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x))))  ∨
  (∃ w : List (List T), ∃ β : List T, ∃ γ : List (symbol T g.nt), ∃ x : List (List (symbol T g.nt)),
    (∀ wᵢ ∈ w, grammar_generates g wᵢ) ∧
    (grammar_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal β ++ γ)) ∧
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = List.map symbol.terminal (List.join w) ++ List.map symbol.terminal β ++ [R] ++
      List.map wrap_sym γ ++ [H] ++ List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x))))  ∨
  (∃ u : List T, u ∈ Language.star (grammar_language g) ∧ α' = List.map symbol.terminal u)  ∨
  (∃ σ : List (symbol T g.nt), α' = List.map wrap_sym σ ++ [R])  ∨
  (∃ ω : List (ns T g.nt), α' = ω ++ [H]) ∧ Z ∉ α' ∧ R ∉ α'  :=
begin
  rcases hyp with ⟨x, valid, cat⟩,
  have no_Z_in_alpha : Z ∉ α,
  {
    intro contr,
    rw cat at contr,
    clear_except contr,
    rw List.mem_append at contr,
    cases contr,
    {
      cases contr,
      {
        exact Z_neq_R contr,
      },
      {
        apply Z_neq_H,
        rw ←List.mem_singleton,
        exact contr,
      },
    },
    {
      exact Z_not_in_join_mpHmmw contr,
    },
  },
  rw cat at *,
  clear cat,
  rcases orig with ⟨r, rin, u, v, bef, aft⟩,

  iterate 2 {
    cases rin,
    {
      exfalso,
      apply no_Z_in_alpha,
      rw bef,
      apply List.mem_append_left,
      apply List.mem_append_left,
      apply List.mem_append_right,
      rw List.mem_singleton,
      rw rin,
      refl,
    },
  },
  cases rin,
  {
    cases x with x₀ L,
    {
      right, right, right,
      rw [List.map_nil, List.map_nil, List.join, List.append_nil] at bef,
      have empty_string : u = [] ∧ v = [],
      {
        rw rin at bef,
        exact uv_nil_of_RH_eq bef,
      },
      rw [empty_string.left, List.nil_append, empty_string.right, List.append_nil] at aft,
      use List.nil,
      rw aft,
      rw [List.map_nil, List.nil_append],
      rw rin,
    },
    {
      right, left,
      use [[], [], x₀, L],
      split,
      {
        intros wᵢ wiin,
        exfalso,
        rw List.mem_nil_iff at wiin,
        exact wiin,
      },
      split,
      {
        rw [List.map_nil, List.nil_append],
        exact valid x₀ (List.mem_cons_self x₀ L),
      },
      split,
      {
        intros xᵢ xiin,
        exact valid xᵢ (List.mem_cons_of_mem x₀ xiin),
      },
      rw aft,
      rw [List.map_nil, List.append_nil, List.join, List.map_nil, List.nil_append],
      rw rin at bef ⊢,
      dsimp only at bef ⊢,
      have u_nil := u_nil_when_RH bef,
      rw [u_nil, List.nil_append] at bef ⊢,
      have eq_v := List.append_inj_right bef (by refl),
      rw ←eq_v,
      rw [List.map_cons, List.map_cons, List.join],
      rw [←List.append_assoc, ←List.append_assoc],
    },
  },
  cases rin,
  {
    cases x with x₀ L,
    {
      right, right, left,
      rw [List.map_nil, List.map_nil, List.join, List.append_nil] at bef,
      have empty_string : u = [] ∧ v = [],
      {
        rw rin at bef,
        exact uv_nil_of_RH_eq bef,
      },
      rw [empty_string.left, List.nil_append, empty_string.right, List.append_nil] at aft,
      use List.nil,
      split,
      {
        use List.nil,
        split,
        {
          refl,
        },
        {
          intros y imposs,
          exfalso,
          exact List.not_mem_nil y imposs,
        },
      },
      {
        rw aft,
        rw List.map_nil,
        rw rin,
      },
    },
    {
      right, right, right, right,
      rw rin at bef,
      dsimp only at bef,
      have u_nil := u_nil_when_RH bef,
      rw [u_nil, List.nil_append] at bef,
      have v_eq := eq.symm (List.append_inj_right bef (by refl)),
      rw [
        u_nil, List.nil_append, v_eq, rin, List.nil_append,
        List.map_cons, List.map_cons, List.join,
        List.append_assoc, List.append_join_append, ←List.append_assoc
      ] at aft,
      split,
      {
        use List.map wrap_sym x₀ ++ (List.map (λ l, [H] ++ l) (List.map (List.map wrap_sym) L)).join,
        rw aft,
        trim,
      },
      rw [List.append_assoc, ←List.append_join_append] at aft,
      rw aft,
      split;
      intro contra;
      rw List.mem_append at contra,
      {
        cases contra,
        {
          exact map_wrap_never_contains_Z contra,
        },
        cases contra,
        {
          exact Z_neq_H contra,
        },
        {
          exact Z_not_in_join_mpHmmw contra,
        },
      },
      {
        cases contra,
        {
          exact map_wrap_never_contains_R contra,
        },
        cases contra,
        {
          exact H_neq_R contra.symm,
        },
        {
          exact R_not_in_join_mpHmmw contra,
        },
      },
    },
  },
  have rin' : r ∈ rules_that_scan_terminals g ∨ r ∈ List.map wrap_gr g.rules,
  {
    rw or_comm,
    rwa ←List.mem_append,
  },
  clear rin,
  cases rin',
  {
    exfalso,
    unfold rules_that_scan_terminals at rin',
    rw List.mem_map at rin',
    rcases rin' with ⟨t, -, form⟩,
    rw ←form at bef,
    dsimp only at bef,
    rw List.append_nil at bef,
    have u_nil : u = [],
    {
      cases u with d l,
      {
        refl,
      },
      exfalso,
      repeat {
        rw List.cons_append at bef,
      },
      rw List.nil_append at bef,
      have btail := List.tail_eq_of_cons_eq bef,
      have imposs := congr_arg (λ l, R ∈ l) btail,
      dsimp only at imposs,
      apply false_of_true_eq_false,
      convert imposs.symm,
      {
        rw [eq_iff_iff, true_iff],
        apply List.mem_append_left,
        apply List.mem_append_left,
        apply List.mem_append_right,
        apply List.mem_singleton_self,
      },
      {
        rw [eq_iff_iff, false_iff],
        intro hyp,
        rw List.mem_cons_iff at hyp,
        cases hyp,
        {
          exact H_neq_R hyp.symm,
        },
        rw List.mem_join at hyp,
        rcases hyp with ⟨p, pin, Rinp⟩,
        rw List.mem_map at pin,
        rcases pin with ⟨q, qin, eq_p⟩,
        rw ←eq_p at Rinp,
        rw List.mem_append at Rinp,
        cases Rinp,
        {
          rw List.mem_map at qin,
          rcases qin with ⟨p', -, eq_q⟩,
          rw ←eq_q at Rinp,
          exact map_wrap_never_contains_R Rinp,
        },
        {
          rw List.mem_singleton at Rinp,
          exact H_neq_R Rinp.symm,
        },
      },
    },
    rw [u_nil, List.nil_append] at bef,
    have second_symbol := congr_fun (congr_arg List.nth bef) 1,
    rw List.nth_append at second_symbol,
    swap, {
      rw [List.length_cons, List.length_singleton],
      exact lt_add_one 1,
    },
    rw List.nth_append at second_symbol,
    swap, {
      rw [List.length_append, List.length_singleton, List.length_singleton],
      exact lt_add_one 1,
    },
    rw List.singleton_append at second_symbol,
    repeat {
      rw List.nth at second_symbol,
    },
    exact symbol.no_confusion (Option.some.inj second_symbol),
  },
  left,
  rw List.mem_map at rin',
  rcases rin' with ⟨r₀, orig_in, wrap_orig⟩,
  unfold wrap_gr at wrap_orig,
  rw ←wrap_orig at *,
  clear wrap_orig,
  dsimp only at bef,
  rcases case_2_match_rule  bef with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩,
  clear bef,
  rw [u_eq, v_eq] at aft,
  use (List.take m x ++ [u₁ ++ r₀.output_string ++ v₁] ++ List.drop m.succ x),
  split,
  {
    intros xᵢ xiin,
    rw List.mem_append_append at xiin,
    cases xiin,
    {
      apply valid,
      exact List.mem_of_mem_take xiin,
    },
    cases xiin,
    swap, {
      apply valid,
      exact List.mem_of_mem_drop xiin,
    },
    rw List.mem_singleton at xiin,
    rw xiin,
    have last_step :
      grammar_transforms g
        (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁)
        (u₁ ++ r₀.output_string ++ v₁),
    {
      use r₀,
      split,
      {
        exact orig_in,
      },
      use [u₁, v₁],
      split;
      refl,
    },
    apply grammar_deri_of_deri_tran _ last_step,
    apply valid (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁),
    exact List.nth_mem xm_eq,
  },
  rw aft,
  repeat {
    rw List.cons_append,
  },
  apply congr_arg2,
  {
    refl,
  },
  repeat {
    rw List.map_append,
  },
  rw List.join_append_append,
  repeat {
    rw List.append_assoc,
  },
  apply congr_arg2,
  {
    refl,
  },
  rw List.nil_append,
  apply congr_arg2,
  {
    rw ←List.map_take,
    refl,
  },
  simp [List.map, List.join, List.singleton_append, List.map_append, List.append_assoc, List.map_map, List.map_drop],
end

private lemma case_3_ni_wb {g : grammar T} {w : List (List T)} {β : List T} {i : Fin 3} :
  @symbol.nonterminal T (nn g.nt) (sum.inr i) ∉
    List.map (@symbol.terminal T (nn g.nt)) w.join ++ List.map (@symbol.terminal T (nn g.nt)) β  :=
begin
  intro contra,
  rw List.mem_append at contra,
  cases contra;
  {
    rw List.mem_map at contra,
    rcases contra with ⟨t, -, imposs⟩,
    exact symbol.no_confusion imposs,
  },
end

private lemma case_3_ni_u {g : grammar T}
    {w : List (List T)} {β : List T} {γ : List (symbol T g.nt)}
    {x : List (List (symbol T g.nt))} {u v : List (ns T g.nt)} {s : ns T g.nt}
    (ass :
      List.map symbol.terminal w.join ++ List.map symbol.terminal β ++ [R] ++ List.map wrap_sym γ ++ [H] ++
        (List.map (++ [H]) (List.map (List.map wrap_sym) x)).join =
      u ++ [R] ++ [s] ++ v
    ) :
  R ∉ u  :=
begin
  intro R_in_u,
  classical,
  have count_R := congr_arg (λ l, List.count_in l R) ass,
  dsimp only at count_R,
  repeat {
    rw List.count_in_append at count_R,
  },
  have R_ni_wb : R ∉ List.map symbol.terminal w.join ++ List.map symbol.terminal β,
  {
    apply @case_3_ni_wb T g,
  },
  rw List.count_in_singleton_eq at count_R,
  rw [List.count_in_singleton_neq H_neq_R, add_zero] at count_R,
  rw ←List.count_in_append at count_R,
  rw [List.count_in_zero_of_notin R_ni_wb, zero_add] at count_R,
  rw [List.count_in_zero_of_notin map_wrap_never_contains_R, add_zero] at count_R,
  rw [zero_Rs_in_the_long_part, add_zero] at count_R,
  have ucR_pos := List.count_in_pos_of_in R_in_u,
  clear_except count_R ucR_pos,
  linarith,
end

private lemma case_3_u_eq_left_side {g : grammar T}
    {w : List (List T)} {β : List T} {γ : List (symbol T g.nt)}
    {x : List (List (symbol T g.nt))} {u v : List (ns T g.nt)} {s : ns T g.nt}
    (ass :
      List.map symbol.terminal w.join ++ List.map symbol.terminal β ++ [R] ++ List.map wrap_sym γ ++ [H] ++
        List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x)) =
      u ++ [symbol.nonterminal (sum.inr 2)] ++ [s] ++ v
    ) :
  u = List.map symbol.terminal w.join ++ List.map (@symbol.terminal T (nn g.nt)) β  :=
begin
  have R_ni_u : R ∉ u,
  {
    exact case_3_ni_u ass,
  },
  have R_ni_wb : R ∉ List.map symbol.terminal w.join ++ List.map symbol.terminal β,
  {
    apply @case_3_ni_wb T g,
  },
  repeat {
    rw List.append_assoc at ass,
  },
  convert congr_arg (List.take u.length) ass.symm,
  {
    rw List.take_left,
  },
  rw ←List.append_assoc,
  rw List.take_left',
  {
    classical,
    have index_of_first_R := congr_arg (List.index_of R) ass,
    rw List.index_of_append_of_notin R_ni_u at index_of_first_R,
    rw @List.singleton_append _ _ ([s] ++ v) at index_of_first_R,
    rw [←R, List.index_of_cons_self, add_zero] at index_of_first_R,
    rw [←List.append_assoc, List.index_of_append_of_notin R_ni_wb] at index_of_first_R,
    rw [List.singleton_append, List.index_of_cons_self, add_zero] at index_of_first_R,
    exact index_of_first_R,
  },
end

private lemma case_3_gamma_nil {g : grammar T}
    {w : List (List T)} {β : List T} {γ : List (symbol T g.nt)}
    {x : List (List (symbol T g.nt))} {u v : List (ns T g.nt)}
    (ass :
      List.map symbol.terminal w.join ++ List.map symbol.terminal β ++ [symbol.nonterminal (sum.inr 2)] ++
        List.map wrap_sym γ ++ [H] ++ List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x)) =
      u ++ [symbol.nonterminal (sum.inr 2)] ++ [H] ++ v
    ) :
  γ = []  :=
begin
  have R_ni_wb : R ∉ List.map symbol.terminal w.join ++ List.map symbol.terminal β,
  {
    apply @case_3_ni_wb T g,
  },
  have H_ni_wb : H ∉ List.map symbol.terminal w.join ++ List.map symbol.terminal β,
  {
    apply @case_3_ni_wb T g,
  },
  have H_ni_wbrg : H ∉
    List.map (@symbol.terminal T (nn g.nt)) w.join ++ List.map symbol.terminal β ++
      [symbol.nonterminal (sum.inr 2)] ++ List.map wrap_sym γ,
  {
    intro contra,
    rw List.mem_append at contra,
    cases contra,
    swap, {
      exact map_wrap_never_contains_H contra,
    },
    rw List.mem_append at contra,
    cases contra,
    {
      exact H_ni_wb contra,
    },
    {
      rw List.mem_singleton at contra,
      exact H_neq_R contra,
    },
  },
  have R_ni_u : @symbol.nonterminal T (nn g.nt) (sum.inr 2) ∉ u,
  {
    exact case_3_ni_u ass,
  },
  have H_ni_u : H ∉ u,
  {
    rw case_3_u_eq_left_side ass,
    exact H_ni_wb,
  },
  classical,
  have first_R := congr_arg (List.index_of R) ass,
  have first_H := congr_arg (List.index_of H) ass,
  repeat {
    rw List.append_assoc (List.map symbol.terminal w.join ++ List.map symbol.terminal β) at first_R,
  },
  rw List.append_assoc
    (List.map symbol.terminal w.join ++ List.map symbol.terminal β ++
      [symbol.nonterminal (sum.inr 2)] ++ List.map wrap_sym γ)
    at first_H,
  rw List.index_of_append_of_notin R_ni_wb at first_R,
  rw List.index_of_append_of_notin H_ni_wbrg at first_H,
  rw [List.cons_append, List.cons_append, List.cons_append, R, List.index_of_cons_self, add_zero] at first_R,
  rw [List.cons_append, List.index_of_cons_self, add_zero] at first_H,
  rw [List.append_assoc u, List.append_assoc u] at first_R first_H,
  rw List.index_of_append_of_notin R_ni_u at first_R,
  rw List.index_of_append_of_notin H_ni_u at first_H,
  rw [List.append_assoc _ [H], List.singleton_append, List.index_of_cons_self, add_zero] at first_R,
  rw [List.append_assoc _ [H], List.singleton_append, ←R, List.index_of_cons_ne _ H_neq_R] at first_H,
  rw [List.singleton_append, H, List.index_of_cons_self] at first_H,
  rw ←first_R at first_H,
  clear_except first_H,
  repeat {
    rw List.length_append at first_H,
  },
  rw List.length_singleton at first_H,
  rw ←add_zero ((List.map symbol.terminal w.join).length + (List.map symbol.terminal β).length + 1) at first_H,
  rw add_right_inj at first_H,
  rw List.length_map at first_H,
  rw List.length_eq_zero at first_H,
  exact first_H,
end

private lemma case_3_v_nil {g : grammar T}
    {w : List (List T)} {β : List T} {u v : List (ns T g.nt)}
    (ass :
      List.map symbol.terminal w.join ++ List.map symbol.terminal β ++ [R] ++ [H] =
      u ++ [symbol.nonterminal (sum.inr 2)] ++ [H] ++ v
    ) :
  v = []  :=
begin
  have rev := congr_arg List.reverse ass,
  repeat {
    rw List.reverse_append at rev,
  },
  repeat {
    rw List.reverse_singleton at rev,
  },
  rw ←List.reverse_eq_nil,
  cases v.reverse with d l,
  {
    refl,
  },
  exfalso,
  rw List.singleton_append at rev,
  have brt := List.tail_eq_of_cons_eq rev,
  have brtt := congr_arg List.tail brt,
  rw List.singleton_append at brtt,
  rw List.tail_cons at brtt,
  cases l with e l',
  {
    change
      (List.map symbol.terminal β).reverse ++ (List.map symbol.terminal w.join).reverse =
      [symbol.nonterminal (sum.inr 2)] ++ u.reverse
    at brtt,
    have imposs := congr_arg (λ a, R ∈ a) brtt,
    dsimp only at imposs,
    apply false_of_true_eq_false,
    convert imposs.symm,
    {
      rw [eq_iff_iff, true_iff],
      apply List.mem_append_left,
      apply List.mem_singleton_self,
    },
    {
      rw [eq_iff_iff, false_iff],
      rw List.mem_append,
      push_neg,
      split;
      {
        rw List.mem_reverse,
        rw List.mem_map,
        push_neg,
        intros t trash,
        apply symbol.no_confusion,
      },
    },
  },
  {
    change _ = _ ++ _ at brtt,
    have imposs := congr_arg (λ a, H ∈ a) brtt,
    dsimp only at imposs,
    apply false_of_true_eq_false,
    convert imposs.symm,
    {
      rw [eq_iff_iff, true_iff],
      apply List.mem_append_right,
      apply List.mem_append_left,
      apply List.mem_singleton_self,
    },
    {
      rw [eq_iff_iff, false_iff],
      rw List.mem_append,
      push_neg,
      split;
      {
        rw List.mem_reverse,
        rw List.mem_map,
        push_neg,
        intros t trash,
        apply symbol.no_confusion,
      },
    },
  },
end

private lemma case_3_false_of_wbr_eq_urz {g : grammar T} {r₀ : grule T g.nt}
    {w : List (List T)} {β : List T} {u z : List (ns T g.nt)}
    (contradictory_equality :
      List.map symbol.terminal w.join ++ List.map symbol.terminal β ++ [R] =
      u ++ List.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ z) :
  false :=
begin
  apply false_of_true_eq_false,
  convert congr_arg ((∈) (symbol.nonterminal (sum.inl r₀.input_N))) contradictory_equality.symm,
  {
    rw [eq_iff_iff, true_iff],
    apply List.mem_append_left,
    apply List.mem_append_right,
    apply List.mem_singleton_self,
  },
  {
    rw [eq_iff_iff, false_iff],
    intro hyp_N_in,
    rw List.mem_append at hyp_N_in,
    cases hyp_N_in,
    swap, {
      rw List.mem_singleton at hyp_N_in,
      exact sum.no_confusion (symbol.nonterminal.inj hyp_N_in),
    },
    rw List.mem_append at hyp_N_in,
    cases hyp_N_in;
    {
      rw List.mem_map at hyp_N_in,
      rcases hyp_N_in with ⟨t, -, impos⟩,
      exact symbol.no_confusion impos,
    },
  },
end

private lemma case_3_match_rule {g : grammar T} {r₀ : grule T g.nt}
    {x : List (List (symbol T g.nt))} {u v : List (ns T g.nt)}
    {w : List (List T)} {β : List T} {γ : List (symbol T g.nt)}
    (hyp :
      List.map symbol.terminal (List.join w) ++ List.map symbol.terminal β ++ [R] ++
        List.map wrap_sym γ ++ [H] ++ List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x)) =
      u ++ List.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++
        List.map wrap_sym r₀.input_R ++ v) :
  (∃ m : ℕ, ∃ u₁ v₁ : List (symbol T g.nt),
    u = List.map symbol.terminal (List.join w) ++ List.map symbol.terminal β ++
        [R] ++ List.map wrap_sym γ ++ [H] ++
        List.join (List.map (++ [H]) (List.take m (List.map (List.map wrap_sym) x))) ++ List.map wrap_sym u₁
    ∧  List.nth x m = some (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁)  ∧
    v = List.map wrap_sym v₁ ++ [H] ++
        List.join (List.map (++ [H]) (List.drop m.succ (List.map (List.map wrap_sym) x)))) ∨
  (∃ u₁ v₁ : List (symbol T g.nt),
    u = List.map symbol.terminal (List.join w) ++ List.map symbol.terminal β ++ [R] ++ List.map wrap_sym u₁
    ∧  γ = u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁  ∧
    v = List.map wrap_sym v₁ ++ [H] ++ List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x)))  :=
begin
  repeat {
    rw List.append_assoc u at hyp,
  },
  rw List.append_eq_append_iff at hyp,
  cases hyp,
  {
    rcases hyp with ⟨u', u_eq, xj_eq⟩,
    left,
    repeat {
      rw ←List.append_assoc at xj_eq,
    },
    by_cases is_x_nil : x = [],
    {
      exfalso,
      rw [is_x_nil, List.map_nil, List.map_nil, List.join] at xj_eq,
      have imposs := congr_arg List.length xj_eq,
      rw List.length at imposs,
      rw List.length_append_append at imposs,
      rw List.length_append_append at imposs,
      rw List.length_singleton at imposs,
      clear_except imposs,
      linarith,
    },
    rcases cases_1_and_2_and_3a_match_aux is_x_nil xj_eq with ⟨m, u₁, v₁, u'_eq, xm_eq, v_eq⟩,
    use [m, u₁, v₁],
    split,
    {
      rw u_eq,
      rw u'_eq,
      rw ←List.append_assoc,
    },
    split,
    {
      exact xm_eq,
    },
    {
      exact v_eq,
    },
  },
  {
    rcases hyp with ⟨v', left_half, right_half⟩,
    have very_middle :
      [symbol.nonterminal (sum.inl r₀.input_N)] = List.map wrap_sym [symbol.nonterminal r₀.input_N],
    {
      rw List.map_singleton,
      refl,
    },
    cases x with x₀ xₗ,
    {
      rw [List.map_nil, List.map_nil, List.join, List.append_nil] at right_half,
      rw ←right_half at left_half,
      have backwards := congr_arg List.reverse left_half,
      clear right_half left_half,
      right,
      repeat {
        rw List.reverse_append at backwards,
      },
      rw [List.reverse_singleton, List.singleton_append] at backwards,
      rw ←List.reverse_reverse v,
      cases v.reverse with e z,
      {
        exfalso,
        rw List.nil_append at backwards,
        rw ←List.map_reverse _ r₀.input_R at backwards,
        cases r₀.input_R.reverse with d l,
        {
          rw [List.map_nil, List.nil_append] at backwards,
          rw List.reverse_singleton (symbol.nonterminal (sum.inl r₀.input_N)) at backwards,
          rw List.singleton_append at backwards,
          have imposs := List.head_eq_of_cons_eq backwards,
          exact sum.no_confusion (symbol.nonterminal.inj imposs),
        },
        {
          rw [List.map_cons, List.cons_append, List.cons_append] at backwards,
          have imposs := List.head_eq_of_cons_eq backwards,
          exact wrap_never_outputs_H imposs.symm,
        },
      },
      rw [List.cons_append, List.cons_append, List.cons.inj_eq] at backwards,
      cases backwards with He backward,
      rw ←He at *,
      clear He e,
      have forward := congr_arg List.reverse backward,
      clear backward,
      repeat {
        rw List.reverse_append at forward,
      },
      repeat {
        rw List.reverse_reverse at forward,
      },
      rw ←List.append_assoc at forward,
      rw List.append_eq_append_iff at forward,
      cases forward,
      swap, {
        exfalso,
        rcases forward with ⟨a, imposs, -⟩,
        rw List.append_assoc u at imposs,
        rw List.append_assoc _ (List.map wrap_sym r₀.input_R) at imposs,
        rw ←List.append_assoc u at imposs,
        rw ←List.append_assoc u at imposs,
        exact case_3_false_of_wbr_eq_urz imposs,
      },
      rcases forward with ⟨a', left_side, gamma_is⟩,
      repeat {
        rw ←List.append_assoc at left_side,
      },
      rw List.append_eq_append_iff at left_side,
      cases left_side,
      {
        exfalso,
        rcases left_side with ⟨a, imposs, -⟩,
        exact case_3_false_of_wbr_eq_urz imposs,
      },
      rcases left_side with ⟨c', the_left, the_a'⟩,
      rw the_a' at gamma_is,
      clear the_a' a',
      rw List.append_assoc at the_left,
      rw List.append_assoc at the_left,
      rw List.append_eq_append_iff at the_left,
      cases the_left,
      {
        exfalso,
        rcases the_left with ⟨a, -, imposs⟩,
        apply false_of_true_eq_false,
        convert congr_arg ((∈) R) imposs.symm,
        {
          rw [eq_iff_iff, true_iff],
          apply List.mem_append_right,
          apply List.mem_append_left,
          apply List.mem_singleton_self,
        },
        {
          rw [eq_iff_iff, false_iff],
          rw List.mem_append,
          push_neg,
          split,
          {
            rw List.mem_map,
            push_neg,
            intros,
            apply wrap_never_outputs_R,
          },
          {
            rw List.mem_singleton,
            intro impos,
            exact sum.no_confusion (symbol.nonterminal.inj impos),
          },
        },
      },
      rcases the_left with ⟨u₀, u_eq, rule_side⟩,
      rw u_eq at *,
      clear u_eq u,
      have zr_eq : z.reverse = List.drop (c' ++ List.map wrap_sym r₀.input_R).length (List.map wrap_sym γ),
      {
        have gamma_suffix := congr_arg (List.drop (c' ++ List.map wrap_sym r₀.input_R).length) gamma_is,
        rw List.drop_left at gamma_suffix,
        exact gamma_suffix.symm,
      },
      cases u₀ with d l,
      {
        exfalso,
        rw List.nil_append at rule_side,
        cases r₀.input_L with d l,
        {
          rw [List.map_nil, List.nil_append] at rule_side,
          have imposs := List.head_eq_of_cons_eq rule_side,
          exact sum.no_confusion (symbol.nonterminal.inj imposs),
        },
        {
          rw [List.map_cons, List.cons_append] at rule_side,
          have imposs := List.head_eq_of_cons_eq rule_side,
          exact wrap_never_outputs_R imposs.symm,
        },
      },
      rw [List.singleton_append, List.cons_append, List.cons.inj_eq] at rule_side,
      cases rule_side with Rd c'_eq,
      rw ←Rd at *,
      clear Rd d,
      rw c'_eq at gamma_is,
      use [List.take l.length γ, List.drop (c' ++ List.map wrap_sym r₀.input_R).length γ],
      split,
      {
        rw ←List.singleton_append,
        have l_from_gamma := congr_arg (List.take l.length) gamma_is,
        repeat {
          rw List.append_assoc at l_from_gamma,
        },
        rw List.take_left at l_from_gamma,
        rw List.map_take,
        rw l_from_gamma,
        rw ←List.append_assoc,
      },
      split,
      {
        rw c'_eq,
        convert_to List.take l.length γ ++ List.drop l.length γ = _,
        {
          symmetry,
          apply List.take_append_drop,
        },
        trim,
        rw zr_eq at gamma_is,
        rw c'_eq at gamma_is,
        repeat {
          rw List.append_assoc at gamma_is,
        },
        have gamma_minus_initial_l := congr_arg (List.drop l.length) gamma_is,
        rw [List.drop_left, very_middle, ←List.map_drop, ←List.map_drop] at gamma_minus_initial_l,
        repeat {
          rw ←List.map_append at gamma_minus_initial_l,
        },
        rw wrap_str_inj gamma_minus_initial_l,
        trim,
        repeat {
          rw List.length_append,
        },
        repeat {
          rw List.length_map,
        },
        repeat {
          rw List.length_append,
        },
        repeat {
          rw List.length_singleton,
        },
        repeat {
          rw add_assoc,
        },
      },
      {
        rw [List.map_nil, List.map_nil, List.join, List.append_nil],
        rw [List.reverse_cons, zr_eq],
        rw List.map_drop,
      },
    },
    by_cases is_v'_nil : v' = [],
    {
      rw [is_v'_nil, List.nil_append] at right_half,
      rw [is_v'_nil, List.append_nil] at left_half,
      left,
      use [0, [], List.drop (r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R).length x₀],
      rw [List.map_cons, List.map_cons, List.join] at right_half,
      split,
      {
        rw [List.map_nil, List.append_nil],
        rw [List.take_zero, List.map_nil, List.join, List.append_nil],
        exact left_half.symm,
      },
      have lengths_trivi :
        List.length (
          List.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ List.map wrap_sym r₀.input_R
        ) =
        List.length (r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R),
      {
        rw [very_middle, ←List.map_append_append],
        apply List.length_map,
      },
      have len_rᵢ_le_len_x₀ :
        (r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R).length ≤ (List.map wrap_sym x₀).length,
      {
        classical,
        have first_H := congr_arg (List.index_of H) right_half,
        rw [List.append_assoc _ [H], List.index_of_append_of_notin map_wrap_never_contains_H] at first_H,
        rw [List.singleton_append, List.index_of_cons_self, add_zero] at first_H,
        rw [very_middle, ←List.map_append_append, List.index_of_append_of_notin map_wrap_never_contains_H] at first_H,
        rw List.length_map at first_H,
        exact Nat.le.intro first_H,
      },
      split,
      {
        rw List.nth,
        apply congr_arg,
        rw List.nil_append,
        convert_to  x₀ =
            List.take (r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R).length x₀ ++
            List.drop (r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R).length x₀,
        {
          trim,
          apply wrap_str_inj,
          rw List.map_append_append,
          have right_left :=
            congr_arg (List.take (r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R).length) right_half,
          rw List.take_left' lengths_trivi at right_left,
          rw [←very_middle, right_left],
          rw List.append_assoc _ [H],
          rw List.take_append_of_le_length len_rᵢ_le_len_x₀,
          rw List.map_take,
        },
        rw List.take_append_drop,
      },
      {
        rw [List.map_cons, List.drop_one, List.tail_cons],
        have right_right :=
            congr_arg (List.drop (r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R).length) right_half,
        rw List.drop_left' lengths_trivi at right_right,
        rw right_right,
        rw List.append_assoc _ [H],
        rw List.drop_append_of_le_length len_rᵢ_le_len_x₀,
        rw List.map_drop,
        rw List.append_assoc _ [H],
        refl,
      },
    },
    right,
    obtain ⟨z, v'_eq⟩ : ∃ z,  v' =
        List.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ List.map wrap_sym r₀.input_R ++ z,
    {
      obtain ⟨v'', without_final_H⟩ : ∃ v'', v' = v'' ++ [H],
      {
        rw List.append_eq_append_iff at left_half,
        cases left_half,
        {
          rcases left_half with ⟨a', -, matters⟩,
          use List.nil,
          cases a' with d l,
          {
            rw List.nil_append at matters ⊢,
            exact matters.symm,
          },
          {
            exfalso,
            have imposs := congr_arg List.length matters,
            rw [List.length_singleton, List.length_append, List.length_cons] at imposs,
            have right_pos := length_ge_one_of_not_nil is_v'_nil,
            clear_except imposs right_pos,
            linarith,
          },
        },
        {
          rcases left_half with ⟨c', -, v_c'⟩,
          exact ⟨c', v_c'⟩,
        },
      },
      rw without_final_H at right_half,
      rw List.append_assoc v'' at right_half,
      have key_prop :
        List.length (
          List.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ List.map wrap_sym r₀.input_R
        ) ≤
        v''.length,
      {
        classical,
        have first_H := congr_arg (List.index_of H) right_half,
        rw [very_middle, ←List.map_append_append, List.index_of_append_of_notin map_wrap_never_contains_H] at first_H,
        have H_not_in_v'' : H ∉ v'',
        {
          rw [without_final_H, ←List.append_assoc] at left_half,
          intro contra,
          apply false_of_true_eq_false,
          convert congr_arg ((∈) H) (List.append_right_cancel left_half).symm,
          {
            rw [eq_iff_iff, true_iff],
            exact List.mem_append_right _ contra,
          },
          {
            clear_except,
            rw [eq_iff_iff, false_iff],
            intro contr,
            iterate 3 {
              rw List.mem_append at contr,
              cases contr,
            },
            iterate 2 {
              rw List.mem_map at contr,
              rcases contr with ⟨t, -, impos⟩,
              exact symbol.no_confusion impos,
            },
            {
              rw List.mem_singleton at contr,
              exact H_neq_R contr,
            },
            {
              rw List.mem_map at contr,
              rcases contr with ⟨s, -, imposs⟩,
              exact wrap_never_outputs_H imposs,
            },
          },
        },
        rw List.index_of_append_of_notin H_not_in_v'' at first_H,
        rw [List.singleton_append, List.index_of_cons_self, add_zero] at first_H,
        rw [very_middle, ←List.map_append_append],
        exact Nat.le.intro first_H,
      },
      obtain ⟨n, key_prop'⟩ := Nat.le.dest key_prop,
      have right_take := congr_arg (List.take v''.length) right_half,
      rw List.take_left at right_take,
      rw ←key_prop' at right_take,
      rw List.take_append at right_take,
      use List.take n v ++ [H],
      rw without_final_H,
      rw ←right_take,
      repeat {
        rw ←List.append_assoc,
      },
    },
    rw v'_eq at right_half,
    rw List.append_assoc _ z at right_half,
    rw List.append_right_inj at right_half,
    rw v'_eq at left_half,
    obtain ⟨u₁, v₁, gamma_parts, z_eq⟩ : ∃ u₁, ∃ v₁,
      List.map wrap_sym γ =
      List.map wrap_sym u₁ ++ (
        List.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++ List.map wrap_sym r₀.input_R
      ) ++ List.map wrap_sym v₁  ∧
      z = List.map wrap_sym v₁ ++ [H],
    {
      repeat {
        rw ←List.append_assoc at left_half,
      },
      rw List.append_assoc _ (List.map wrap_sym γ) at left_half,
      rw List.append_assoc _ _ z at left_half,
      rw List.append_eq_append_iff at left_half,
      cases left_half,
      swap, {
        exfalso,
        rcases left_half with ⟨c', imposs, -⟩,
        exact case_3_false_of_wbr_eq_urz imposs,
      },
      rcases left_half with ⟨a', lhl, lhr⟩,
      have lhl' := congr_arg List.reverse lhl,
      repeat {
        rw List.reverse_append at lhl',
      },
      rw List.reverse_singleton at lhl',
      rw ←List.reverse_reverse a' at lhr,
      cases a'.reverse with d' l',
      {
        exfalso,
        rw List.nil_append at lhl',
        rw [List.singleton_append, List.reverse_singleton, List.singleton_append] at lhl',
        have imposs := List.head_eq_of_cons_eq lhl',
        exact sum.no_confusion (symbol.nonterminal.inj imposs),
      },
      rw List.singleton_append at lhl',
      rw List.cons_append at lhl',
      rw List.cons.inj_eq at lhl',
      cases lhl' with eq_d' lhl'',
      rw ←eq_d' at lhr,
      clear eq_d' d',
      rw ←List.append_assoc l' at lhl'',
      rw List.append_eq_append_iff at lhl'',
      cases lhl'',
      swap, {
        exfalso,
        rcases lhl'' with ⟨c'', imposs, -⟩,
        rw List.reverse_singleton at imposs,
        apply false_of_true_eq_false,
        convert congr_arg ((∈) R) imposs.symm,
        {
          rw [eq_iff_iff, true_iff],
          apply List.mem_append_left,
          apply List.mem_append_right,
          apply List.mem_singleton_self,
        },
        {
          rw [eq_iff_iff, false_iff],
          rw List.mem_reverse,
          apply map_wrap_never_contains_R,
        },
      },
      rcases lhl'' with ⟨b', lhlr', lhll'⟩,
      rw List.reverse_singleton at lhlr',
      have lhlr := congr_arg List.reverse lhlr',
      rw [List.reverse_append, List.reverse_append, List.reverse_reverse] at lhlr,
      rw [List.reverse_singleton, List.singleton_append] at lhlr,
      rw ←List.reverse_reverse b' at lhll',
      cases b'.reverse with d'' l'',
      {
        exfalso,
        rw List.nil_append at lhlr,
        cases r₀.input_L with d l,
        {
          rw List.map_nil at lhlr,
          exact List.no_confusion lhlr,
        },
        rw List.map_cons at lhlr,
        have imposs := List.head_eq_of_cons_eq lhlr,
        exact wrap_never_outputs_R imposs.symm,
      },
      rw List.cons_append at lhlr,
      rw List.cons.inj_eq at lhlr,
      cases lhlr with eq_d'' lve,
      rw ←eq_d'' at lhll',
      clear eq_d'' d'',
      have lhll := congr_arg List.reverse lhll',
      rw [List.reverse_reverse, List.reverse_append, List.reverse_reverse, List.reverse_append,
          List.reverse_reverse, List.reverse_reverse] at lhll,
      rw lhll at *,
      clear lhll u,
      rw List.reverse_cons at lhr,
      rw lve at lhr,
      use List.take l''.length γ,
      use List.drop (l''
            ++ List.map wrap_sym r₀.input_L
            ++ [symbol.nonterminal (sum.inl r₀.input_N)]
            ++ List.map wrap_sym r₀.input_R
          ).length γ,
      have z_expr :  z =
        List.map wrap_sym (
            List.drop (l''
              ++ List.map wrap_sym r₀.input_L
              ++ [symbol.nonterminal (sum.inl r₀.input_N)]
              ++ List.map wrap_sym r₀.input_R
            ).length γ
          ) ++ [H],
      {
        have lhdr :=
          congr_arg
            (List.drop (l''
              ++ List.map wrap_sym r₀.input_L
              ++ [symbol.nonterminal (sum.inl r₀.input_N)]
              ++ List.map wrap_sym r₀.input_R
            ).length) lhr,
        rw List.drop_append_of_le_length at lhdr,
        {
          rw [List.map_drop, lhdr, ←List.append_assoc, List.drop_left],
        },
        have lhr' := congr_arg List.reverse lhr,
        repeat {
          rw List.reverse_append at lhr',
        },
        rw List.reverse_singleton at lhr',
        cases z.reverse with d l,
        {
          exfalso,
          rw [List.nil_append, List.singleton_append] at lhr',
          rw ←List.map_reverse _ r₀.input_R at lhr',
          cases r₀.input_R.reverse with dᵣ lᵣ,
          {
            rw [List.map_nil, List.nil_append, List.reverse_singleton, List.singleton_append] at lhr',
            have imposs := List.head_eq_of_cons_eq lhr',
            exact sum.no_confusion (symbol.nonterminal.inj imposs),
          },
          {
            rw [List.map_cons, List.cons_append] at lhr',
            have imposs := List.head_eq_of_cons_eq lhr',
            exact wrap_never_outputs_H imposs.symm,
          },
        },
        repeat {
          rw List.length_append,
        },
        have contra_len := congr_arg List.length lhr',
        repeat {
          rw List.length_append at contra_len,
        },
        repeat {
          rw List.length_reverse at contra_len,
        },
        repeat {
          rw List.length_singleton at contra_len,
        },
        rw List.length_cons at contra_len,
        rw List.length_singleton,
        clear_except contra_len,
        linarith,
      },
      split,
      swap, {
        exact z_expr,
      },
      rw z_expr at lhr,
      have gamma_expr :  List.map wrap_sym γ =
        l'' ++ List.map wrap_sym r₀.input_L ++ [symbol.nonterminal (sum.inl r₀.input_N)] ++
          (List.map wrap_sym r₀.input_R ++
            (List.map wrap_sym
              (List.drop (l''
                ++ List.map wrap_sym r₀.input_L
                ++ [symbol.nonterminal (sum.inl r₀.input_N)]
                ++ List.map wrap_sym r₀.input_R
              ).length γ))),
      {
        repeat {
          rw ←List.append_assoc at lhr,
        },
        repeat {
          rw ←List.append_assoc,
        },
        exact List.append_right_cancel lhr,
      },
      rw gamma_expr,
      trim,
      have almost := congr_arg (List.take l''.length) gamma_expr.symm,
      repeat {
        rw List.append_assoc at almost,
      },
      rw List.take_left at almost,
      rw List.map_take,
      exact almost,
    },
    use [u₁, v₁],
    split, swap, split,
    {
      apply wrap_str_inj,
      rwa [
        very_middle, ←List.map_append_append, ←List.map_append_append,
        ←List.append_assoc, ←List.append_assoc
      ] at gamma_parts,
    },
    {
      rwa z_eq at right_half,
    },
    rw gamma_parts at left_half,
    rw List.append_assoc (List.map wrap_sym u₁) at left_half,
    rw ←List.append_assoc _ (List.map wrap_sym u₁) at left_half,
    rw List.append_assoc _ _ [H] at left_half,
    have left_left := congr_arg (List.take u.length) left_half,
    rw List.take_left at left_left,
    rw List.take_left' at left_left,
    {
      exact left_left.symm,
    },
    have lh_len := congr_arg List.length left_half,
    repeat {
      rw List.length_append at lh_len,
    },
    repeat {
      rw List.length_singleton at lh_len,
    },
    have cut_off_end : z.length = (List.map wrap_sym v₁).length + 1,
    {
      simpa using congr_arg List.length z_eq,
    },
    rw cut_off_end at lh_len,
    repeat {
      rw List.length_append,
    },
    rw List.length_singleton,
    repeat {
      rw add_assoc at lh_len,
    },
    iterate 3 {
      rw ←add_assoc at lh_len,
    },
    rwa add_left_inj at lh_len,
  },
end

private lemma star_case_3 {g : grammar T} {α α' : List (ns T g.nt)}
    (orig : grammar_transforms (star_grammar g) α α')
    (hyp : ∃ w : List (List T), ∃ β : List T, ∃ γ : List (symbol T g.nt), ∃ x : List (List (symbol T g.nt)),
      (∀ wᵢ ∈ w, grammar_generates g wᵢ) ∧
      (grammar_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal β ++ γ)) ∧
      (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
      (α = List.map symbol.terminal (List.join w) ++ List.map symbol.terminal β ++ [R] ++
        List.map wrap_sym γ ++ [H] ++ List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x)))) :
  (∃ w : List (List T), ∃ β : List T, ∃ γ : List (symbol T g.nt), ∃ x : List (List (symbol T g.nt)),
    (∀ wᵢ ∈ w, grammar_generates g wᵢ) ∧
    (grammar_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal β ++ γ)) ∧
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α' = List.map symbol.terminal (List.join w) ++ List.map symbol.terminal β ++ [R] ++
      List.map wrap_sym γ ++ [H] ++ List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x))))  ∨
  (∃ u : List T, u ∈ Language.star (grammar_language g) ∧ α' = List.map symbol.terminal u)  ∨
  (∃ σ : List (symbol T g.nt), α' = List.map wrap_sym σ ++ [R])  ∨
  (∃ ω : List (ns T g.nt), α' = ω ++ [H]) ∧ Z ∉ α' ∧ R ∉ α'  :=
begin
  rcases hyp with ⟨w, β, γ, x, valid_w, valid_middle, valid_x, cat⟩,
  have no_Z_in_alpha : Z ∉ α,
  {
    intro contr,
    rw cat at contr,
    clear_except contr,
    repeat {
      rw List.mem_append at contr,
    },
    iterate 5 {
      cases contr,
    },
    any_goals {
      rw List.mem_map at contr,
      rcases contr with ⟨s, -, imposs⟩,
    },
    {
      exact symbol.no_confusion imposs,
    },
    {
      exact symbol.no_confusion imposs,
    },
    {
      rw List.mem_singleton at contr,
      exact Z_neq_R contr,
    },
    {
      exact wrap_never_outputs_Z imposs,
    },
    {
      rw List.mem_singleton at contr,
      exact Z_neq_H contr,
    },
    {
      exact Z_not_in_join_mpHmmw contr,
    },
  },
  rw cat at *,
  clear cat,
  rcases orig with ⟨r, rin, u, v, bef, aft⟩,

  iterate 2 {
    cases rin,
    {
      exfalso,
      apply no_Z_in_alpha,
      rw bef,
      apply List.mem_append_left,
      apply List.mem_append_left,
      apply List.mem_append_right,
      rw List.mem_singleton,
      rw rin,
      refl,
    },
  },
  cases rin,
  {
    rw rin at bef aft,
    dsimp only at bef aft,
    rw List.append_nil at bef,
    have gamma_nil_here := case_3_gamma_nil bef,
    cases x with x₀ L,
    {
      right, right, left,
      rw [gamma_nil_here, List.map_nil, List.append_nil] at bef,
      rw [List.map_nil, List.map_nil, List.join, List.append_nil] at bef,
      have v_nil := case_3_v_nil bef,
      rw [v_nil, List.append_nil] at bef aft,
      use List.map symbol.terminal w.join ++ List.map symbol.terminal β,
      rw aft,
      have bef_minus_H := List.append_right_cancel bef,
      have bef_minus_RH := List.append_right_cancel bef_minus_H,
      rw ←bef_minus_RH,
      rw [List.map_append, List.map_map, List.map_map],
      refl,
    },
    {
      left,
      use [w ++ [β], x₀, L],
      split,
      {
        intros wᵢ wiin,
        rw List.mem_append at wiin,
        cases wiin,
        {
          exact valid_w wᵢ wiin,
        },
        {
          rw List.mem_singleton at wiin,
          rw wiin,
          rw [gamma_nil_here, List.append_nil] at valid_middle,
          exact valid_middle,
        },
      },
      split,
      {
        rw [List.map_nil, List.nil_append],
        exact valid_x x₀ (List.mem_cons_self x₀ L),
      },
      split,
      {
        intros xᵢ xiin,
        exact valid_x xᵢ (List.mem_cons_of_mem x₀ xiin),
      },
      rw [List.map_nil, List.append_nil],
      rw aft,
      have u_eq : u = List.map (@symbol.terminal T (nn g.nt)) w.join ++ List.map (@symbol.terminal T (nn g.nt)) β,
      {
        exact case_3_u_eq_left_side bef,
      },
      have v_eq : v = List.join (List.map (++ [H]) (List.map (List.map wrap_sym) (x₀ :: L))),
      {
        rw u_eq at bef,
        rw [gamma_nil_here, List.map_nil, List.append_nil] at bef,
        exact (List.append_left_cancel bef).symm,
      },
      rw [u_eq, v_eq],
      rw [List.join_append, List.map_append, List.join_singleton],
      rw [List.map_cons, List.map_cons, List.join],
      rw [←List.append_assoc, ←List.append_assoc],
      refl,
    },
  },
  cases rin,
  {
    rw rin at bef aft,
    dsimp only at bef aft,
    rw List.append_nil at bef aft,
    have gamma_nil_here := case_3_gamma_nil bef,
    rw ←List.reverse_reverse x at *,
    cases x.reverse with xₘ L,
    {
      right, left,
      rw [gamma_nil_here, List.map_nil, List.append_nil] at bef,
      rw [List.reverse_nil, List.map_nil, List.map_nil, List.join, List.append_nil] at bef,
      have v_nil := case_3_v_nil bef,
      rw [v_nil, List.append_nil] at bef aft,
      use List.join w ++ β,
      split,
      {
        use w ++ [β],
        split,
        {
          rw List.join_append,
          rw List.join_singleton,
        },
        {
          intros y y_in,
          rw List.mem_append at y_in,
          cases y_in,
          {
            exact valid_w y y_in,
          },
          {
            rw List.mem_singleton at y_in,
            rw y_in,
            rw [gamma_nil_here, List.append_nil] at valid_middle,
            exact valid_middle,
          },
        },
      },
      {
        rw aft,
        have bef_minus_H := List.append_right_cancel bef,
        have bef_minus_RH := List.append_right_cancel bef_minus_H,
        rw ←bef_minus_RH,
        rw List.map_append,
      },
    },
    {
      right, right, right,
      rw List.reverse_cons at bef,
      rw aft,
      have Z_ni_wb : Z ∉ List.map (@symbol.terminal T (nn g.nt)) w.join ++ List.map symbol.terminal β,
      {
        apply case_3_ni_wb,
      },
      have R_ni_wb : R ∉ List.map (@symbol.terminal T (nn g.nt)) w.join ++ List.map symbol.terminal β,
      {
        apply case_3_ni_wb,
      },
      have u_eq : u = List.map (@symbol.terminal T (nn g.nt)) w.join ++ List.map symbol.terminal β,
      {
        exact case_3_u_eq_left_side bef,
      },
      have v_eq : v = List.join (List.map (++ [H]) (List.map (List.map wrap_sym) (L.reverse ++ [xₘ]))),
      {
        rw u_eq at bef,
        rw [gamma_nil_here, List.map_nil, List.append_nil] at bef,
        exact (List.append_left_cancel bef).symm,
      },
      rw [u_eq, v_eq],
      split,
      {
        use List.map symbol.terminal w.join ++ List.map symbol.terminal β ++
            List.join (List.map (++ [H]) (List.map (List.map wrap_sym) L.reverse)) ++ List.map wrap_sym xₘ,
        rw [
          List.map_append, List.map_append, List.join_append,
          List.map_singleton, List.map_singleton, List.join_singleton,
          ←List.append_assoc, ←List.append_assoc
        ], refl,
      },
      split,
      {
        intro contra,
        rw List.mem_append at contra,
        cases contra,
        {
          exact Z_ni_wb contra,
        },
        {
          exact Z_not_in_join_mpHmmw contra,
        },
      },
      {
        intro contra,
        rw List.mem_append at contra,
        cases contra,
        {
          exact R_ni_wb contra,
        },
        {
          exact R_not_in_join_mpHmmw contra,
        },
      },
    },
  },
  have rin' : r ∈ rules_that_scan_terminals g ∨ r ∈ List.map wrap_gr g.rules,
  {
    rw or_comm,
    rwa ←List.mem_append,
  },
  clear rin,
  cases rin',
  {
    left,
    unfold rules_that_scan_terminals at rin',
    rw List.mem_map at rin',
    rcases rin' with ⟨t, -, r_is⟩,
    rw ←r_is at bef aft,
    dsimp only at bef aft,
    rw List.append_nil at bef,
    have u_matches : u = List.map (@symbol.terminal T (nn g.nt)) w.join ++ List.map symbol.terminal β,
    {
      exact case_3_u_eq_left_side bef,
    },
    have tv_matches :
      [symbol.terminal t] ++ v =
      List.map wrap_sym γ ++ [H] ++ List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x)),
    {
      rw u_matches at bef,
      repeat {
        rw List.append_assoc at bef,
      },
      have almost := List.append_left_cancel (List.append_left_cancel (List.append_left_cancel bef)),
      rw ←List.append_assoc at almost,
      exact almost.symm,
    },
    cases γ with a δ,
    {
      exfalso,
      rw [List.map_nil, List.nil_append, List.singleton_append, List.singleton_append] at tv_matches,
      have t_matches := List.head_eq_of_cons_eq tv_matches,
      exact symbol.no_confusion t_matches,
    },
    rw [List.singleton_append, List.map_cons, List.cons_append, List.cons_append] at tv_matches,
    use [w, β ++ [t], δ, x],
    split,
    {
      exact valid_w,
    },
    split,
    {
      have t_matches' := List.head_eq_of_cons_eq tv_matches,
      cases a;
      unfold wrap_sym at t_matches',
      {
        have t_eq_a := symbol.terminal.inj t_matches',
        rw [t_eq_a, List.map_append, List.map_singleton, List.append_assoc, List.singleton_append],
        exact valid_middle,
      },
      {
        exfalso,
        exact symbol.no_confusion t_matches',
      },
    },
    split,
    {
      exact valid_x,
    },
    rw aft,
    rw u_matches,
    rw [List.map_append, List.map_singleton],
    have v_matches := List.tail_eq_of_cons_eq tv_matches,
    rw v_matches,
    simp [List.append_assoc],
  },
  left,
  rw List.mem_map at rin',
  rcases rin' with ⟨r₀, orig_in, wrap_orig⟩,
  unfold wrap_gr at wrap_orig,
  rw ←wrap_orig at *,
  clear wrap_orig,
  cases case_3_match_rule bef,
  {
    rcases h with ⟨m, u₁, v₁, u_eq, xm_eq, v_eq⟩,
    clear bef,
    dsimp only at aft,
    rw [u_eq, v_eq] at aft,
    use w,
    use β,
    use γ,
    use (List.take m x ++ [u₁ ++ r₀.output_string ++ v₁] ++ List.drop m.succ x),
    split,
    {
      exact valid_w,
    },
    split,
    {
      exact valid_middle,
    },
    split,
    {
      intros xᵢ xiin,
      rw List.mem_append_append at xiin,
      cases xiin,
      {
        apply valid_x,
        exact List.mem_of_mem_take xiin,
      },
      cases xiin,
      swap, {
        apply valid_x,
        exact List.mem_of_mem_drop xiin,
      },
      {
        rw List.mem_singleton at xiin,
        rw xiin,
        have last_step :
          grammar_transforms g
            (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁)
            (u₁ ++ r₀.output_string ++ v₁),
        {
          use r₀,
          split,
          {
            exact orig_in,
          },
          use [u₁, v₁],
          split;
          refl,
        },
        apply grammar_deri_of_deri_tran _ last_step,
        apply valid_x (u₁ ++ r₀.input_L ++ [symbol.nonterminal r₀.input_N] ++ r₀.input_R ++ v₁),
        exact List.nth_mem xm_eq,
      },
    },
    {
      rw aft,
      trim,
      rw [
        List.map_append_append,
        List.map_append_append,
        List.join_append_append,
        ←List.map_take,
        ←List.map_drop,
        List.map_singleton,
        List.map_singleton,
        List.join_singleton,
        List.map_append_append,
        ←List.append_assoc,
        ←List.append_assoc,
        ←List.append_assoc
      ],
    },
  },
  {
    rcases h with ⟨u₁, v₁, u_eq, γ_eq, v_eq⟩,
    clear bef,
    dsimp only at aft,
    rw [u_eq, v_eq] at aft,
    use w,
    use β,
    use u₁ ++ r₀.output_string ++ v₁,
    use x,
    split,
    {
      exact valid_w,
    },
    split,
    {
      apply grammar_deri_of_deri_tran valid_middle,
      rw γ_eq,
      use r₀,
      split,
      {
        exact orig_in,
      },
      use [List.map symbol.terminal β ++ u₁, v₁],
      split,
      repeat {
        rw ←List.append_assoc,
      },
    },
    split,
    {
      exact valid_x,
    },
    {
      rw aft,
      trim,
      rw List.map_append_append,
    },
  },
end

private lemma star_case_4 {g : grammar T} {α α' : List (ns T g.nt)}
    (orig : grammar_transforms (star_grammar g) α α')
    (hyp : ∃ u : List T, u ∈ (grammar_language g).star ∧ α = List.map symbol.terminal u) :
  false :=
begin
  rcases hyp with ⟨w, -, alpha_of_w⟩,
  rw alpha_of_w at orig,
  rcases orig with ⟨r, -, u, v, bef, -⟩,
  simpa using congr_arg (λ l, symbol.nonterminal r.input_N ∈ l) bef,
end

private lemma star_case_5 {g : grammar T} {α α' : List (ns T g.nt)}
    (orig : grammar_transforms (star_grammar g) α α')
    (hyp : ∃ σ : List (symbol T g.nt), α = List.map wrap_sym σ ++ [R]) :
  (∃ σ : List (symbol T g.nt), α' = List.map wrap_sym σ ++ [R])  :=
begin
  rcases hyp with ⟨w, ends_with_R⟩,
  rcases orig with ⟨r, rin, u, v, bef, aft⟩,
  rw ends_with_R at bef,
  clear ends_with_R,
  iterate 2 {
    cases rin,
    {
      exfalso,
      rw rin at bef,
      simp only [List.append_nil] at bef,
      have imposs := congr_arg (λ l, Z ∈ l) bef,
      simp only [List.mem_append] at imposs,
      rw List.mem_singleton at imposs,
      rw List.mem_singleton at imposs,
      apply false_of_true_eq_false,
      convert imposs.symm,
      {
        unfold Z,
        rw [eq_self_iff_true, or_true, true_or],
      },
      {
        rw [eq_iff_iff, false_iff],
        push_neg,
        split,
        {
          apply map_wrap_never_contains_Z,
        },
        {
          exact Z_neq_R,
        },
      },
    },
  },
  iterate 2 {
    cases rin,
    {
      exfalso,
      rw rin at bef,
      dsimp only at bef,
      rw List.append_nil at bef,
      have rev := congr_arg List.reverse bef,
      repeat {
        rw List.reverse_append at rev,
      },
      repeat {
        rw List.reverse_singleton at rev,
      },
      rw List.singleton_append at rev,
      cases v.reverse with d l,
      {
        rw List.nil_append at rev,
        rw List.singleton_append at rev,
        have tails := List.tail_eq_of_cons_eq rev,
        rw ←List.map_reverse at tails,
        cases w.reverse with d' l',
        {
          rw List.map_nil at tails,
          have imposs := congr_arg List.length tails,
          rw [List.length, List.length_append, List.length_singleton] at imposs,
          clear_except imposs,
          linarith,
        },
        {
          rw List.map_cons at tails,
          rw List.singleton_append at tails,
          have heads := List.head_eq_of_cons_eq tails,
          exact wrap_never_outputs_R heads,
        },
      },
      {
        have tails := List.tail_eq_of_cons_eq rev,
        have H_in_tails := congr_arg (λ l, H ∈ l) tails,
        dsimp only at H_in_tails,
        rw List.mem_reverse at H_in_tails,
        apply false_of_true_eq_false,
        convert H_in_tails.symm,
        {
          rw [eq_iff_iff, true_iff],
          apply List.mem_append_right,
          apply List.mem_append_left,
          apply List.mem_singleton_self,
        },
        {
          rw [eq_iff_iff, false_iff],
          intro hyp_H_in,
          exact map_wrap_never_contains_H hyp_H_in,
        },
      },
    },
  },
  change r ∈ List.map wrap_gr g.rules ++ rules_that_scan_terminals g at rin,
  rw List.mem_append at rin,
  cases rin,
  {
    rw List.mem_map at rin,
    rcases rin with ⟨r₀, -, r_of_r₀⟩,
    rw List.append_eq_append_iff at bef,
    cases bef,
    {
      rcases bef with ⟨x, ur_eq, singleR⟩,
      by_cases is_x_nil : x = [],
      {
        have v_is_R : v = [R],
        {
          rw [is_x_nil, List.nil_append] at singleR,
          exact singleR.symm,
        },
        rw v_is_R at aft,
        rw [is_x_nil, List.append_nil] at ur_eq,
        have u_from_w : u = List.take u.length (List.map wrap_sym w),
        { -- do not extract out of `cases bef`
          repeat {
            rw List.append_assoc at ur_eq,
          },
          have tak := congr_arg (List.take u.length) ur_eq,
          rw List.take_left at tak,
          exact tak,
        },
        rw ←List.map_take at u_from_w,
        rw u_from_w at aft,
        rw ←r_of_r₀ at aft,
        dsimp only [wrap_gr] at aft,
        use List.take u.length w ++ r₀.output_string,
        rw List.map_append,
        exact aft,
      },
      {
        exfalso,
        have x_is_R : x = [R],
        {
          by_cases is_v_nil : v = [],
          {
            rw [is_v_nil, List.append_nil] at singleR,
            exact singleR.symm,
          },
          {
            exfalso,
            have imposs := congr_arg List.length singleR,
            rw List.length_singleton at imposs,
            rw List.length_append at imposs,
            have xl_ge_one := length_ge_one_of_not_nil is_x_nil,
            have vl_ge_one := length_ge_one_of_not_nil is_v_nil,
            clear_except imposs xl_ge_one vl_ge_one,
            linarith,
          },
        },
        rw x_is_R at ur_eq,
        have ru_eq := congr_arg List.reverse ur_eq,
        repeat {
          rw List.reverse_append at ru_eq,
        },
        repeat {
          rw List.reverse_singleton at ru_eq,
          rw List.singleton_append at ru_eq,
        },
        rw ←r_of_r₀ at ru_eq,
        dsimp only [wrap_gr, R] at ru_eq,
        rw ←List.map_reverse at ru_eq,
        cases r₀.input_R.reverse with d l,
        {
          rw [List.map_nil, List.nil_append] at ru_eq,
          have imposs := List.head_eq_of_cons_eq ru_eq,
          exact sum.no_confusion (symbol.nonterminal.inj imposs),
        },
        {
          have imposs := List.head_eq_of_cons_eq ru_eq,
          cases d;
          unfold wrap_sym at imposs,
          {
            exact symbol.no_confusion imposs,
          },
          {
            exact sum.no_confusion (symbol.nonterminal.inj imposs),
          },
        },
      },
    },
    {
      rcases bef with ⟨y, w_eq, v_eq⟩,
      have u_from_w : u = List.take u.length (List.map wrap_sym w),
      { -- do not extract out of `cases bef`
        repeat {
          rw List.append_assoc at w_eq,
        },
        have tak := congr_arg (List.take u.length) w_eq,
        rw List.take_left at tak,
        exact tak.symm,
      },
      have y_from_w :
        y = List.drop (u ++ r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R).length (List.map wrap_sym w),
      {
        have drp := congr_arg (List.drop (u ++ r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R).length) w_eq,
        rw List.drop_left at drp,
        exact drp.symm,
      },
      -- weird that `u_from_w` and `y_from_w` did not unify their type parameters in the same way
      rw u_from_w at aft,
      rw y_from_w at v_eq,
      rw v_eq at aft,
      use List.take u.length w ++ r₀.output_string ++
          List.drop (u ++ r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R).length w,
      rw List.map_append_append,
      rw List.map_take,
      rw List.map_drop,
      rw aft,
      trim, -- fails to identify `List.take u.length (List.map wrap_sym w)` of defin-equal type parameters
      rw ←r_of_r₀,
      dsimp only [wrap_gr],
      refl, -- outside level `(symbol T (star_grammar g).nt) = (ns T g.nt) = (symbol T (nn g.nt))`
    },
  },
  {
    exfalso,
    unfold rules_that_scan_terminals at rin,
    rw List.mem_map at rin,
    rcases rin with ⟨t, -, eq_r⟩,
    rw ←eq_r at bef,
    clear eq_r,
    dsimp only at bef,
    rw List.append_nil at bef,
    have rev := congr_arg List.reverse bef,
    repeat {
      rw List.reverse_append at rev,
    },
    repeat {
      rw List.reverse_singleton at rev,
    },
    rw List.singleton_append at rev,
    cases v.reverse with d l,
    {
      rw List.nil_append at rev,
      rw List.singleton_append at rev,
      have tails := List.tail_eq_of_cons_eq rev,
      rw ←List.map_reverse at tails,
      cases w.reverse with d' l',
      {
        rw List.map_nil at tails,
        have imposs := congr_arg List.length tails,
        rw [List.length, List.length_append, List.length_singleton] at imposs,
        clear_except imposs,
        linarith,
      },
      {
        rw List.map_cons at tails,
        rw List.singleton_append at tails,
        have heads := List.head_eq_of_cons_eq tails,
        exact wrap_never_outputs_R heads,
      },
    },
    {
      have tails := List.tail_eq_of_cons_eq rev,
      have R_in_tails := congr_arg (λ l, R ∈ l) tails,
      dsimp only at R_in_tails,
      rw List.mem_reverse at R_in_tails,
      apply false_of_true_eq_false,
      convert R_in_tails.symm,
      {
        rw [eq_iff_iff, true_iff],
        apply List.mem_append_right,
        apply List.mem_append_right,
        apply List.mem_append_left,
        apply List.mem_singleton_self,
      },
      {
        rw [eq_iff_iff, false_iff],
        intro hyp_R_in,
        exact map_wrap_never_contains_R hyp_R_in,
      },
    },
  },
end

private lemma star_case_6 {g : grammar T} {α α' : List (ns T g.nt)}
    (orig : grammar_transforms (star_grammar g) α α')
    (hyp : (∃ ω : List (ns T g.nt), α = ω ++ [H]) ∧ Z ∉ α ∧ R ∉ α) :
  (∃ ω : List (ns T g.nt), α' = ω ++ [H]) ∧ Z ∉ α' ∧ R ∉ α'  :=
begin
  rcases hyp with ⟨⟨w, ends_with_H⟩, no_Z, no_R⟩,
  rcases orig with ⟨r, rin, u, v, bef, aft⟩,
  iterate 2 {
    cases rin,
    {
      exfalso,
      rw rin at bef,
      simp only [List.append_nil] at bef,
      rw bef at no_Z,
      apply no_Z,
      apply List.mem_append_left,
      apply List.mem_append_right,
      apply List.mem_singleton_self,
    },
  },
  iterate 2 {
    cases rin,
    {
      exfalso,
      rw rin at bef,
      dsimp only at bef,
      rw List.append_nil at bef,
      rw bef at no_R,
      apply no_R,
      apply List.mem_append_left,
      apply List.mem_append_left,
      apply List.mem_append_right,
      apply List.mem_singleton_self,
    },
  },
  change r ∈ List.map wrap_gr g.rules ++ rules_that_scan_terminals g at rin,
  rw List.mem_append at rin,
  cases rin,
  {
    rw ends_with_H at bef,
    rw List.mem_map at rin,
    rcases rin with ⟨r₀, -, r_of_r₀⟩,
    split,
    swap, {
      split,
      {
        rw aft,
        intro contra,
        rw List.mem_append at contra,
        rw List.mem_append at contra,
        cases contra,
        swap, {
          apply no_Z,
          rw ends_with_H,
          rw bef,
          rw List.mem_append,
          right,
          exact contra,
        },
        cases contra,
        {
          apply no_Z,
          rw ends_with_H,
          rw bef,
          repeat {
            rw List.append_assoc,
          },
          rw List.mem_append,
          left,
          exact contra,
        },
        rw ←r_of_r₀ at contra,
        unfold wrap_gr at contra,
        rw List.mem_map at contra,
        rcases contra with ⟨s, -, imposs⟩,
        cases s,
        {
          unfold wrap_sym at imposs,
          exact symbol.no_confusion imposs,
        },
        {
          unfold wrap_sym at imposs,
          unfold Z at imposs,
          rw symbol.nonterminal.inj_eq at imposs,
          exact sum.no_confusion imposs,
        },
      },
      {
        rw aft,
        intro contra,
        rw List.mem_append at contra,
        rw List.mem_append at contra,
        cases contra,
        swap, {
          apply no_R,
          rw ends_with_H,
          rw bef,
          rw List.mem_append,
          right,
          exact contra,
        },
        cases contra,
        {
          apply no_R,
          rw ends_with_H,
          rw bef,
          repeat {
            rw List.append_assoc,
          },
          rw List.mem_append,
          left,
          exact contra,
        },
        rw ←r_of_r₀ at contra,
        unfold wrap_gr at contra,
        rw List.mem_map at contra,
        rcases contra with ⟨s, -, imposs⟩,
        cases s,
        {
          unfold wrap_sym at imposs,
          exact symbol.no_confusion imposs,
        },
        {
          unfold wrap_sym at imposs,
          unfold R at imposs,
          rw symbol.nonterminal.inj_eq at imposs,
          exact sum.no_confusion imposs,
        },
      },
    },
    use u ++ r.output_string ++ v.take (v.length - 1),
    rw aft,
    trim,
    have vlnn : v.length ≥ 1,
    {
      by_contradiction contra,
      have v_nil := zero_of_not_ge_one contra,
      rw List.length_eq_zero at v_nil,
      rw v_nil at bef,
      rw ←r_of_r₀ at bef,
      rw List.append_nil at bef,
      unfold wrap_gr at bef,
      have rev := congr_arg List.reverse bef,
      clear_except rev,
      repeat {
        rw List.reverse_append at rev,
      },
      rw ←List.map_reverse _ r₀.input_R at rev,
      rw List.reverse_singleton at rev,
      cases r₀.input_R.reverse with d l,
      {
        have H_eq_N : H = symbol.nonterminal (sum.inl r₀.input_N),
        {
          rw [List.map_nil, List.nil_append,
            List.reverse_singleton, List.singleton_append, List.singleton_append,
            List.cons.inj_eq] at rev,
          exact rev.left,
        },
        unfold H at H_eq_N,
        have inr_eq_inl := symbol.nonterminal.inj H_eq_N,
        exact sum.no_confusion inr_eq_inl,
      },
      {
        rw List.map_cons at rev,
        have H_is : H = wrap_sym d,
        {
          rw [List.singleton_append, List.cons_append, List.cons.inj_eq] at rev,
          exact rev.left,
        },
        unfold H at H_is,
        cases d;
        unfold wrap_sym at H_is,
        {
          exact symbol.no_confusion H_is,
        },
        {
          rw symbol.nonterminal.inj_eq at H_is,
          exact sum.no_confusion H_is,
        },
      },
    },
    convert_to List.take (v.length - 1) v ++ List.drop (v.length - 1) v = List.take (v.length - 1) v ++ [H],
    {
      rw List.take_append_drop,
    },
    trim,
    have bef_rev := congr_arg List.reverse bef,
    repeat {
      rw List.reverse_append at bef_rev,
    },
    have bef_rev_tak := congr_arg (List.take 1) bef_rev,
    rw List.take_left' at bef_rev_tak,
    swap, {
      rw List.length_reverse,
      apply List.length_singleton,
    },
    rw List.take_append_of_le_length at bef_rev_tak,
    swap, {
      rw List.length_reverse,
      exact vlnn,
    },
    rw List.reverse_take _ vlnn at bef_rev_tak,
    rw List.reverse_eq_iff at bef_rev_tak,
    rw List.reverse_reverse at bef_rev_tak,
    exact bef_rev_tak.symm,
  },
  {
    exfalso,
    unfold rules_that_scan_terminals at rin,
    rw List.mem_map at rin,
    rcases rin with ⟨t, -, eq_r⟩,
    rw ←eq_r at bef,
    dsimp only at bef,
    rw List.append_nil at bef,
    rw bef at no_R,
    apply no_R,
    apply List.mem_append_left,
    apply List.mem_append_left,
    apply List.mem_append_right,
    apply List.mem_singleton_self,
  },
end

private lemma star_induction {g : grammar T} {α : List (ns T g.nt)}
    (ass : grammar_derives (star_grammar g) [Z] α) :
  (∃ x : List (List (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α = [Z] ++ List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x))))  ∨
  (∃ x : List (List (symbol T g.nt)),
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α = [R, H] ++ List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x))))  ∨
  (∃ w : List (List T), ∃ β : List T, ∃ γ : List (symbol T g.nt), ∃ x : List (List (symbol T g.nt)),
    (∀ wᵢ ∈ w, grammar_generates g wᵢ) ∧
    (grammar_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal β ++ γ)) ∧
    (∀ xᵢ ∈ x, grammar_derives g [symbol.nonterminal g.initial] xᵢ) ∧
    (α = List.map symbol.terminal (List.join w) ++ List.map symbol.terminal β ++ [R] ++
      List.map wrap_sym γ ++ [H] ++ List.join (List.map (++ [H]) (List.map (List.map wrap_sym) x))))  ∨
  (∃ u : List T, u ∈ Language.star (grammar_language g) ∧ α = List.map symbol.terminal u)  ∨
  (∃ σ : List (symbol T g.nt), α = List.map wrap_sym σ ++ [R])  ∨
  (∃ ω : List (ns T g.nt), α = ω ++ [H]) ∧ Z ∉ α ∧ R ∉ α  :=
begin
  induction ass with a b trash orig ih,
  {
    left,
    use List.nil,
    split,
    {
      intros y imposs,
      exfalso,
      exact List.not_mem_nil y imposs,
    },
    {
      refl,
    },
  },
  cases ih,
  {
    rw ←or_assoc,
    left,
    exact star_case_1 orig ih,
  },
  cases ih,
  {
    right,
    exact star_case_2 orig ih,
  },
  cases ih,
  {
    right, right,
    exact star_case_3 orig ih,
  },
  cases ih,
  {
    exfalso,
    exact star_case_4 orig ih,
  },
  cases ih,
  {
    right, right, right, right, left,
    exact star_case_5 orig ih,
  },
  {
    right, right, right, right, right,
    exact star_case_6 orig ih,
  },
end

end hard_direction


/-- The class of recursively-enumerable languages is closed under the Kleene star. -/
theorem RE_of_star_RE (L : Language T) :
  is_RE L  →  is_RE L.star  :=
begin
  rintro ⟨g, hg⟩,
  use star_grammar g,

  apply Set.eq_of_subSetOf_subset,
  {
    -- prove `L.star ⊇` here
    intros w hyp,
    unfold grammar_language at hyp,
    rw Set.mem_SetOf_eq at hyp,
    have result := star_induction hyp,
    clear hyp,
    cases result,
    {
      exfalso,
      rcases result with ⟨x, -, contr⟩,
      cases w with d l,
      {
        tauto,
      },
      rw List.map_cons at contr,
      have terminal_eq_Z : symbol.terminal d = Z,
      {
        exact List.head_eq_of_cons_eq contr,
      },
      exact symbol.no_confusion terminal_eq_Z,
    },
    cases result,
    {
      exfalso,
      rcases result with ⟨x, -, contr⟩,
      cases w with d l,
      {
        tauto,
      },
      rw List.map_cons at contr,
      have terminal_eq_R : symbol.terminal d = R,
      {
        exact List.head_eq_of_cons_eq contr,
      },
      exact symbol.no_confusion terminal_eq_R,
    },
    cases result,
    {
      exfalso,
      rcases result with ⟨α, β, γ, x, -, -, -, contr⟩,
      have output_contains_R : R ∈ List.map symbol.terminal w,
      {
        rw contr,
        apply List.mem_append_left,
        apply List.mem_append_left,
        apply List.mem_append_left,
        apply List.mem_append_right,
        apply List.mem_cons_self,
      },
      rw List.mem_map at output_contains_R,
      rcases output_contains_R with ⟨t, -, terminal_eq_R⟩,
      exact symbol.no_confusion terminal_eq_R,
    },
    cases result,
    {
      rcases result with ⟨u, win, map_eq_map⟩,
      have w_eq_u : w = u,
      {
        have st_inj : function.injective (@symbol.terminal T (star_grammar g).nt),
        {
          apply symbol.terminal.inj,
        },
        rw ←List.map_injective_iff at st_inj,
        exact st_inj map_eq_map,
      },
      rw [w_eq_u, ←hg],
      exact win,
    },
    cases result,
    {
      exfalso,
      cases result with σ contr,
      have last_symbols := congr_fun (congr_arg List.nth (congr_arg List.reverse contr)) 0,
      rw [
        ←List.map_reverse,
        List.reverse_append,
        List.reverse_singleton,
        List.singleton_append,
        List.nth,
        List.nth_map
      ] at last_symbols,
      cases w.reverse.nth 0,
      {
        rw Option.map_none' at last_symbols,
        exact Option.no_confusion last_symbols,
      },
      {
        rw Option.map_some' at last_symbols,
        have terminal_eq_R := Option.some.inj last_symbols,
        exact symbol.no_confusion terminal_eq_R,
      },
    },
    {
      exfalso,
      rcases result with ⟨⟨ω, contr⟩, -⟩,
      have last_symbols := congr_fun (congr_arg List.nth (congr_arg List.reverse contr)) 0,
      rw [
        ←List.map_reverse,
        List.reverse_append,
        List.reverse_singleton,
        List.singleton_append,
        List.nth,
        List.nth_map
      ] at last_symbols,
      cases w.reverse.nth 0,
      {
        rw Option.map_none' at last_symbols,
        exact Option.no_confusion last_symbols,
      },
      {
        rw Option.map_some' at last_symbols,
        have terminal_eq_H := Option.some.inj last_symbols,
        exact symbol.no_confusion terminal_eq_H,
      },
    },
  },
  {
    -- prove `L.star ⊆` here
    intros p ass,
    unfold grammar_language,
    rw Language.star at ass,
    rw Set.mem_SetOf_eq at ⊢ ass,
    rcases ass with ⟨w, w_join, parts_in_L⟩,
    let v := w.reverse,
    have v_reverse : v.reverse = w,
    {
      apply List.reverse_reverse,
    },
    rw ←v_reverse at *,
    rw w_join,
    clear w_join p,
    unfold grammar_generates,
    rw ←hg at parts_in_L,
    cases short_induction parts_in_L with derived terminated,
    apply grammar_deri_of_deri_deri derived,
    apply grammar_deri_of_tran_deri,
    {
      use (star_grammar g).rules.nthLe 1 (by dec_trivial),
      split,
      {
        apply List.nthLe_mem,
      },
      use [[], (List.map (++ [H]) (List.map (List.map symbol.terminal) v.reverse)).join],
      split,
      {
        rw List.reverse_reverse,
        refl,
      },
      {
        refl, -- binds the implicit argument of `grammar_deri_of_tran_deri`
      },
    },
    rw List.nil_append,
    rw v_reverse,
    have final_step :
      grammar_transforms (star_grammar g)
        (List.map symbol.terminal w.join ++ [R, H])
        (List.map symbol.terminal w.join),
    {
      use (star_grammar g).rules.nthLe 3 (by dec_trivial),
      split_ile,
      use [List.map symbol.terminal w.join, List.nil],
      split,
      {
        trim,
      },
      {
        have out_nil : ((star_grammar g).rules.nthLe 3 _).output_string = [],
        {
          refl,
        },
        rw [List.append_nil, out_nil, List.append_nil],
      },
    },
    apply grammar_deri_of_deri_tran _ final_step,
    convert_to
      grammar_derives (star_grammar g)
        ([R] ++ ([H] ++ (List.map (++ [H]) (List.map (List.map symbol.terminal) w)).join))
        (List.map symbol.terminal w.join ++ [R, H]),
    have rebracket :
      [H] ++ (List.map (++ [H]) (List.map (List.map symbol.terminal) w)).join =
      (List.map (λ v, [H] ++ v) (List.map (List.map symbol.terminal) w)).join ++ [H],
    {
      apply List.append_join_append,
    },
    rw rebracket,
    apply terminal_scan_aux,
    intros v vin t tin,
    rw ←List.mem_reverse at vin,
    exact terminated v vin t tin,
  },
end
