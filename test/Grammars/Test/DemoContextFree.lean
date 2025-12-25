import Grammars.Classes.ContextFree.Basics.Toolbox
import Grammars.Utilities.ListUtils
import Grammars.Utilities.WrittenByOthers.TrimAssoc


private def a_ : Fin 3 := 0
private def a : symbol (Fin 3) (Fin 2) := symbol.terminal a_

private def b_ : Fin 3 := 1
private def b : symbol (Fin 3) (Fin 2) := symbol.terminal b_

private def c_ : Fin 3 := 2
private def c : symbol (Fin 3) (Fin 2) := symbol.terminal c_

private def S_ : Fin 2 := 0
private def S : symbol (Fin 3) (Fin 2) := symbol.nonterminal S_

private def R_ : Fin 2 := 1
private def R : symbol (Fin 3) (Fin 2) := symbol.nonterminal R_

private def gr_add : CF_grammar (Fin 3) :=
CF_grammar.mk (Fin 2) S_ [
  (S_, [a, S, c]),
  (S_, [R]),
  (R_, [b, R, c]),
  (R_, [])
]

example : CF_generates gr_add [a_, a_, b_, c_, c_, c_] :=
begin
  unfold gr_add,

  apply CF_deri_of_tran_deri,
  {
    use (S_, [a, S, c]),
    split_ile,
    use [[], []],
    simp,
  },

  apply CF_deri_of_tran_deri,
  {
    use (S_, [a, S, c]),
    split_ile,
    use [[a], [c]],
    rw S,
    simp,
  },

  apply CF_deri_of_tran_deri,
  {
    use (S_, [R]),
    split_ile,
    use [[a, a], [c, c]],
    simp,
  },

  apply CF_deri_of_tran_deri,
  {
    use (R_, [b, R, c]),
    split_ile,
    use [[a, a], [c, c]],
    rw R,
    simp,
  },

  apply CF_deri_of_tran,
  {
    use (R_, []),
    split_ile,
    use [[a, a, b], [c, c, c]],
    repeat { try {split}, try {refl} },
  },
end


private def anbmcnm (n m : ℕ) : List (Fin 3) :=
List.repeat a_ n ++ List.repeat b_ m ++ List.repeat c_ (n + m)

private def language_add : Language (Fin 3) :=
λ x, ∃ n m : ℕ, x = anbmcnm n m

example : [a_, a_, b_, c_, c_, c_] ∈ language_add :=
begin
  use 2,
  use 1,
  refl,
end

example : CF_language gr_add = language_add :=
begin
  ext,

  split,
  {
    -- prove `x ∈ CF_language gr_add → x ∈ language_add` here
    intro ass,
    change CF_derives gr_add [S] (List.map symbol.terminal x) at ass,

    have possib : ∀ w : List (symbol (Fin 3) gr_add.nt),
      CF_derives gr_add [S] w →
        (∃ i : ℕ, w = List.repeat a i ++ [S] ++ List.repeat c i) ∨
        (∃ i j : ℕ, w = List.repeat a i ++ List.repeat b j ++ [R] ++ List.repeat c (i + j)) ∨
        (∃ i j : ℕ, w = List.repeat a i ++ List.repeat b j ++ List.repeat c (i + j)),
    {
      intros w hyp,
      induction hyp with y z irr step ih,
      {
        left,
        use 0,
        refl,
      },
      cases step with rule foo,
      cases foo with rule_in bar,
      cases bar with u baz,
      cases baz with v hyp,
      cases hyp with hyp_bef hyp_aft,

      cases ih with case₁ caseᵣ,
      {
        -- the case `List.repeat a i ++ [S] ++ List.repeat c i` matches 1st and 2nd rule
        cases rule_in,
        {
          left,
          cases case₁ with i the_case,
          rw List.append_assoc at the_case,
          use i + 1,
          have almost : z = List.repeat a i ++ [a, S, c] ++ List.repeat c i,
          {
            rw hyp_bef at the_case,
            rw hyp_aft,
            rw rule_in at *,
            have u_must : u = List.repeat a i,
            {
              dsimp only at *,
              rw ←S at *,
              have indexS: (u ++ [S] ++ v).nth u.length = some S,
              {
                rw List.append_assoc,
                rw List.nth_append_right (le_of_eq rfl),
                rw tsub_self,
                refl,
              },
              cases @trichotomous ℕ (<) _ (List.length u) i with hlt hge,
              {
                exfalso,
                rw the_case at indexS,
                rw ←List.nth_take hlt at indexS,
                rw List.take_append_of_le_length (le_of_eq (List.length_repeat a i).symm) at indexS,
                rw List.take_repeat at indexS,
                rw min_self at indexS,
                rw ←List.length_repeat a i at hlt,
                have please : (List.repeat a i).nth_le u.length hlt = S,
                {
                  rw List.nth_le_nth hlt at indexS,
                  injection indexS,
                },
                rw List.nth_le_repeat a hlt at please,
                injection please,
              },
              cases hge.symm with hgt heq,
              {
                exfalso,
                rw the_case at indexS,
                have rightend : u.length < (List.repeat a i ++ [S] ++ List.repeat c i).length,
                {
                  have thelength := congr_arg List.length the_case,
                  rw List.append_assoc at thelength,
                  rw List.length_append at thelength,
                  rw List.append_assoc,
                  rw ←thelength,
                  rw List.length_append,
                  rw List.length_singleton,
                  rw ←add_assoc,
                  apply lt_of_lt_of_le,
                  {
                    exact lt_add_one u.length,
                  },
                  exact le_self_add,
                },
                rw ←List.append_assoc at indexS,
                rw List.nth_le_nth rightend at indexS,
                injection indexS with continue,
                have mala : (List.repeat a i ++ [S]).length ≤ u.length,
                {
                  rw List.length_append,
                  rw List.length_singleton,
                  rw List.length_repeat a i,
                  rw ←nat.succ_le_iff at hgt,
                  apply hgt,
                },
                rw List.nth_le_append_right mala at continue,
                finish,
              },
              rw List.append_assoc at the_case,
              apply List.append_inj_left the_case,
              rw heq,
              finish,
            },
            have v_must : v = List.repeat c i,
            {
              rw u_must at the_case,
              rw List.append_assoc at the_case,
              rw List.append_right_inj (List.repeat a i) at the_case,
              rw ←S at the_case,
              rw List.append_right_inj [S] at the_case,
              exact the_case,
            },
            rw u_must,
            rw v_must,
          },
          rw List.repeat_add,
          change z = List.repeat a i ++ [a] ++ [S] ++ List.repeat c (i + 1),
          rw add_comm,
          rw List.repeat_add,
          change z = List.repeat a i ++ [a] ++ [S] ++ ([c] ++ List.repeat c i),
          rw ←List.append_assoc,
          rw List.append_assoc (List.repeat a i) [a],
          rw List.append_assoc (List.repeat a i) ([a] ++ [S]),
          convert almost,
        },
        cases rule_in,
        {
          right,
          left,
          cases case₁ with i the_case,
          use i,
          use 0,
          simp,
          have u_must : u = List.repeat a i,
          {
            have indexS: (u ++ [S] ++ v).nth u.length = some S,
            {
              rw List.append_assoc,
              rw List.nth_append_right (le_of_eq rfl),
              rw tsub_self,
              refl,
            },
            cases @trichotomous ℕ (<) _ (List.length u) i with hlt hge,
            {
              exfalso,
              rw hyp_bef at the_case,
              rw rule_in at *,
              rw ←List.nth_take hlt at indexS,
              simp at the_case,
              change u ++ ([S] ++ v) = List.repeat a i ++ ([S] ++ List.repeat c i) at the_case,
              rw List.append_assoc at indexS,
              rw the_case at indexS,
              rw List.take_append_of_le_length (le_of_eq (List.length_repeat a i).symm) at indexS,
              rw List.take_repeat at indexS,
              rw min_self at indexS,
              rw ←List.length_repeat a i at hlt,
              have please : (List.repeat a i).nth_le u.length hlt = S,
              {
                rw List.nth_le_nth hlt at indexS,
                injection indexS,
              },
              rw List.nth_le_repeat a hlt at please,
              injection please,
            },
            cases hge.symm with hgt heq,
            {
              exfalso,
              rw List.append_assoc at the_case,
              rw hyp_bef at the_case,
              rw rule_in at *,
              change u ++ [S] ++ v = List.repeat a i ++ S :: List.repeat c i at the_case,
              rw the_case at indexS,
              have rightend : u.length < (List.repeat a i ++ [S] ++ List.repeat c i).length,
              {
                have thelength := congr_arg List.length the_case,
                rw List.append_assoc at thelength,
                rw List.length_append at thelength,
                rw List.append_assoc,
                change u.length < (List.repeat a i ++ S :: List.repeat c i).length,
                rw ←thelength,
                rw List.length_append,
                rw List.length_singleton,
                rw ←add_assoc,
                apply lt_of_lt_of_le,
                {
                  exact lt_add_one u.length,
                },
                exact le_self_add,
              },
              change (List.repeat a i ++ ([S] ++ List.repeat c i)).nth u.length = some S at indexS,
              rw ←List.append_assoc at indexS,
              rw List.nth_le_nth rightend at indexS,
              injection indexS with continue,
              have mala : (List.repeat a i ++ [S]).length ≤ u.length,
              {
                rw List.length_append,
                rw List.length_singleton,
                rw List.length_repeat a i,
                rw ←nat.succ_le_iff at hgt,
                apply hgt,
              },
              rw List.nth_le_append_right mala at continue,
              finish,
            },
            rw List.append_assoc at the_case,
            rw hyp_bef at the_case,
            rw List.append_assoc at the_case,
            apply List.append_inj_left the_case,
            rw heq,
            rw List.length_repeat a i,
          },
          have v_must : v = List.repeat c i,
          {
            rw List.append_assoc at the_case,
            rw hyp_bef at the_case,
            rw List.append_assoc at the_case,
            rw u_must at the_case,
            rw List.append_right_inj (List.repeat a i) at the_case,
            rw rule_in at the_case,
            change [S] ++ v = [S] ++ List.repeat c i at the_case,
            rw List.append_right_inj [S] at the_case,
            exact the_case,
          },
          rw hyp_aft,
          rw u_must,
          rw v_must,
          rw rule_in,
          simp,
        },
        cases rule_in,
        any_goals { try { cases rule_in },
          exfalso,
          rw rule_in at hyp_bef,
          simp at hyp_bef,
          cases case₁ with i the_case,
          rw the_case at hyp_bef,
          have contra := congr_arg (λ lis, R ∈ lis) hyp_bef,
          rw ←R at contra,
          simp at contra,
          cases contra,
          {
            rw List.mem_repeat at contra,
            have triv : R ≠ a,
            {
              apply symbol.no_confusion,
            },
            exact triv contra.right,
          },
          cases contra,
          {
            injection contra with contr,
            injection contr with cont,
            simp at cont,
            exact cont,
          },
          {
            rw List.mem_repeat at contra,
            have triv : R ≠ c,
            {
              apply symbol.no_confusion,
            },
            exact triv contra.right,
          },
        },
        exfalso,
        exact (List.mem_nil_iff rule).1 rule_in,
      },
      cases caseᵣ with case₂ case₃,
      {
        -- the case `List.repeat a i ++ List.repeat b j ++ [R] ++ List.repeat c (i + j)` matches 3rd and 4th rule
        cases rule_in,
        any_goals { try { cases rule_in },
          exfalso,
          rw rule_in at hyp_bef,
          simp at hyp_bef,
          cases case₂ with i foo,
          cases foo with j y_eq,
          rw y_eq at hyp_bef,
          have contra := congr_arg (λ lis, S ∈ lis) hyp_bef,
          rw ←S at contra,
          simp at contra,
          cases contra,
          {
            rw List.mem_repeat at contra,
            have triv : S ≠ a,
            {
              apply symbol.no_confusion,
            },
            exact triv contra.right,
          },
          cases contra,
          {
            rw List.mem_repeat at contra,
            have triv : S ≠ b,
            {
              apply symbol.no_confusion,
            },
            exact triv contra.right,
          },
          cases contra,
          {
            injection contra with contr,
            injection contr with cont,
            simp at cont,
            exact cont,
          },
          {
            rw List.mem_repeat at contra,
            have triv : S ≠ c,
            {
              apply symbol.no_confusion,
            },
            exact triv contra.right,
          },
        },

        cases rule_in,
        any_goals { try { cases rule_in },
          rw rule_in at *,
          simp at *,
          cases case₂ with i foo,
          cases foo with j y_form,
          rw y_form at hyp_bef,

          have indexR: (u ++ [R] ++ v).nth u.length = some R,
          {
            rw List.append_assoc,
            rw List.nth_append_right (le_of_eq rfl),
            rw tsub_self,
            refl,
          },
          have u_eq : u = List.repeat a i ++ List.repeat b j,
          {
            cases @trichotomous ℕ (<) _ u.length (i + j) with hlt rest,
            {
              exfalso,
              rw ←List.nth_take hlt at indexR,
              have h_len : u.length < (List.repeat a i ++ List.repeat b j).length,
              {
                rw List.length_append,
                rw List.length_repeat,
                rw List.length_repeat,
                exact hlt,
              },
              have propos : (List.repeat a i ++ List.repeat b j).nth_le u.length h_len = R,
              {
                change List.repeat a i ++ (List.repeat b j ++ R :: List.repeat c (i + j)) = u ++ ([R] ++ v) at hyp_bef,
                rw ←List.append_assoc u [R] v at hyp_bef,
                rw ←hyp_bef at indexR,
                rw ←List.append_assoc at indexR,
                have take_beg :
                  List.take (i + j) (List.repeat a i ++ List.repeat b j ++ R :: List.repeat c (i + j)) =
                  (List.repeat a i ++ List.repeat b j),
                {
                  have len_ij : (List.repeat a i ++ List.repeat b j).length = i + j,
                  {
                    rw List.length_append,
                    rw List.length_repeat,
                    rw List.length_repeat,
                  },
                  rw List.take_append_of_le_length (le_of_eq len_ij.symm),
                  rw List.take_all_of_le,
                  exact le_of_eq len_ij,
                },
                rw take_beg at indexR,
                rw List.nth_le_nth h_len at indexR,
                injection indexR,
              },
              have yes_R : R ∈ (List.repeat a i ++ List.repeat b j),
              {
                let positive := List.nth_le_mem (List.repeat a i ++ List.repeat b j) u.length h_len,
                rw propos at positive,
                exact positive,
              },
              have not_R : R ∉ (List.repeat a i ++ List.repeat b j),
              {
                rw List.mem_append,
                push_neg,
                split,
                {
                  have nidRa : R ≠ a,
                  {
                    apply symbol.no_confusion,
                  },
                  by_contradiction hyp,
                  rw List.mem_repeat at hyp,
                  exact nidRa hyp.right,
                },
                {
                  have nidRb : R ≠ b,
                  {
                    apply symbol.no_confusion,
                  },
                  by_contradiction hyp,
                  rw List.mem_repeat at hyp,
                  exact nidRb hyp.right,
                },
              },
              exact not_R yes_R,
            },
            cases rest.symm with hgt heq,
            {
              exfalso,
              have yes_Rc : R ∈ List.repeat c (i + j),
              {
                change
                  List.repeat a i ++ (List.repeat b j ++ R :: List.repeat c (i + j)) = u ++ ([R] ++ v)
                  at hyp_bef,
                rw ←List.append_assoc u [R] v at hyp_bef,
                rw ←hyp_bef at indexR,
                rw ←List.append_assoc at indexR,
                change
                  (List.repeat a i ++ List.repeat b j ++ ([R] ++ List.repeat c (i + j))).nth u.length = some R
                  at indexR,
                rw ←List.append_assoc at indexR,
                rw List.nth_append_right at indexR,
                {
                  simp at indexR,
                  have trouble_len : (u.length - (i + (j + 1))) < (List.repeat c (i + j)).length,
                  {
                    rw List.length_repeat,
                    have lengths_sum : u.length ≤ i + j + i + j,
                    {
                      let lengs := congr_arg List.length hyp_bef,
                      repeat {
                        rw List.length_append at lengs,
                      },
                      rw List.length_repeat at lengs,
                      rw List.length_repeat at lengs,
                      simp at lengs,
                      linarith,
                    },
                    linarith,
                  },
                  rw List.nth_le_nth trouble_len at indexR,
                  {
                    finish,
                  },
                },
                rw List.length_append,
                rw List.length_append,
                rw List.length_repeat,
                rw List.length_repeat,
                convert hgt,
              },
              have not_Rc : R ∉ List.repeat c (i + j),
              {
                by_contradiction hyp,
                rw List.mem_repeat at hyp,
                have nidRc : R ≠ c,
                {
                  apply symbol.no_confusion,
                },
                exact nidRc hyp.right,
              },
              exact not_Rc yes_Rc,
            },
            rw ←List.append_assoc at hyp_bef,
            have lenlen : (List.repeat a i ++ List.repeat b j).length = u.length,
            {
              rw List.length_append,
              rw List.length_repeat,
              rw List.length_repeat,
              exact heq.symm,
            },
            symmetry,
            exact List.append_inj_left hyp_bef lenlen,
          },
          have v_eq : v = List.repeat c (i + j),
          {
            rw u_eq at hyp_bef,
            rw ←List.append_assoc at hyp_bef,
            rw List.append_right_inj (List.repeat a i ++ List.repeat b j) at hyp_bef,
            symmetry,
            exact List.tail_eq_of_cons_eq hyp_bef,
          },
          rw u_eq at hyp_aft,
          rw v_eq at hyp_aft,
          rw hyp_aft,
        },

        {
          right,
          left,
          use i,
          use j + 1,
          have bpp : List.repeat b (j + 1) = List.repeat b j ++ [b],
          {
            rw List.repeat_add b j 1,
            refl,
          },
          have cpp : List.repeat c (i + (j + 1)) = [c] ++ List.repeat c (i + j),
          {
            rw ←add_assoc,
            rw add_comm,
            rw List.repeat_add c 1 (i + j),
            refl,
          },
          rw bpp,
          rw cpp,
          rw List.append_assoc,
          apply congr_arg (λ lis, List.repeat a i ++ lis),
          rw List.append_assoc,
          apply congr_arg (λ lis, List.repeat b j ++ lis),
          rw List.singleton_append,
          rw List.singleton_append,
        },

        cases rule_in,
        {
          right,
          right,
          use i,
          use j,
          rw List.append_assoc,
        },

        exfalso,
        exact (List.mem_nil_iff rule).1 rule_in,
      },
      {
        -- the remaining case `List.repeat a i ++ List.repeat b j ++ List.repeat c (i + j)` does not match any rule
        exfalso,
        rw hyp_bef at case₃,
        cases case₃ with i foo,
        cases foo with j the_case,
        have contra := congr_arg (λ lis, symbol.nonterminal rule.fst ∈ lis) the_case,
        simp at contra,
        cases contra,
        {
          have neq : symbol.nonterminal rule.fst ≠ a,
          {
            apply symbol.no_confusion,
          },
          rw List.mem_repeat at contra,
          apply neq,
          exact contra.right,
        },
        cases contra,
        {
          have neq : symbol.nonterminal rule.fst ≠ b,
          {
            apply symbol.no_confusion,
          },
          rw List.mem_repeat at contra,
          apply neq,
          exact contra.right,
        },
        {
          have neq : symbol.nonterminal rule.fst ≠ c,
          {
            apply symbol.no_confusion,
          },
          rw List.mem_repeat at contra,
          apply neq,
          exact contra.right,
        },
      },
    },

    specialize possib (List.map symbol.terminal x) ass,
    cases possib with imposs rest,
    {
      exfalso,
      cases imposs with i hyp,
      have contra := congr_arg (λ xs, S ∈ xs) hyp,
      simp at contra,
      finish,
    },
    cases rest with imposs' necess,
    {
      exfalso,
      cases imposs' with i rest,
      cases rest with j hyp,
      have contra := congr_arg (λ xs, R ∈ xs) hyp,
      simp at contra,
      finish,
    },
    cases necess with n foobar,
    use n,
    cases foobar with m keyprop,
    use m,
    unfold anbmcnm,
    unfold a b c at keyprop,
    rw ←List.map_repeat symbol.terminal a_ n at keyprop,
    rw ←List.map_repeat symbol.terminal b_ m at keyprop,
    rw ←List.map_repeat symbol.terminal c_ (n + m) at keyprop,
    rw ←List.map_append at keyprop,
    rw ←List.map_append at keyprop,

    ext1 k,
    have kprop := congr_fun (congr_arg List.nth keyprop) k,
    rw List.nth_map at kprop,
    rw List.nth_map at kprop,

    cases x.nth k,
    {
      cases (List.repeat a_ n ++ List.repeat b_ m ++ List.repeat c_ (n + m)).nth k,
      {
        refl,
      },
      {
        exfalso,
        injection kprop,
      },
    },
    {
      cases (List.repeat a_ n ++ List.repeat b_ m ++ List.repeat c_ (n + m)).nth k,
      {
        exfalso,
        injection kprop,
      },
      {
        injection kprop,
        injection h_1,
        rw h_2,
      },
    },
  },
  {
    -- prove `x ∈ CF_language gr_add ← x ∈ language_add` here
    rintro ⟨n, m, hyp⟩,
    rw hyp,
    have epoch_a : ∀ i : ℕ, CF_derives gr_add [S] ((List.repeat a i) ++ [S] ++ (List.repeat c i)),
    {
      intro i,
      induction i with n' ih,
      {
        apply CF_deri_self,
      },
      apply CF_deri_of_deri_tran ih,

      use (S_, [a, S, c]),
      split_ile,
      use [List.repeat a n', List.repeat c n'],
      split,
      {
        refl,
      },
      rw [
        List.repeat_succ_eq_append_singleton a,
        List.repeat_succ_eq_singleton_append c,
        List.append_assoc,
        List.append_assoc,
        ←List.append_assoc [S],
        ←List.append_assoc [a],
        ←List.append_assoc (List.repeat a n')
      ],
      refl,
    },
    have epoch_b : ∀ j : ℕ, CF_derives gr_add [R] ((List.repeat b j) ++ [R] ++ (List.repeat c j)),
    {
      intro j,
      induction j with m' jh,
      {
        apply CF_deri_self,
      },
      apply CF_deri_of_deri_tran jh,

      use (R_, [b, R, c]),
      split_ile,
      use [List.repeat b m', List.repeat c m'],
      split,
      {
        refl,
      },
      rw [
        List.repeat_succ_eq_append_singleton b,
        List.repeat_succ_eq_singleton_append c,
        List.append_assoc,
        List.append_assoc,
        ←List.append_assoc [R],
        ←List.append_assoc [b],
        ←List.append_assoc (List.repeat b m')
      ],
      refl,
    },
    unfold CF_language,
    rw Set.mem_SetOf_eq,
    unfold CF_generates,
    unfold CF_generates_str,
    have obtain_sum :
      CF_derives gr_add
        [symbol.nonterminal gr_add.initial]
        ((List.repeat a n) ++ (List.repeat b m) ++ [R] ++ (List.repeat c (n + m))),
    {
      have middle_step : CF_derives gr_add
        ((List.repeat a n) ++ [S] ++ (List.repeat c n))
        ((List.repeat a n) ++ [R] ++ (List.repeat c n)),
      {
        apply CF_deri_with_prefix_and_postfix,
        apply CF_deri_of_tran,
        use (S_, [R]),
        split_ile,
        use [[], []],
        split;
        refl,
      },
      apply CF_deri_of_deri_deri,
      {
        specialize epoch_a n,
        finish,
      },
      apply CF_deri_of_deri_deri,
      {
        finish,
      },
      change
        CF_derives gr_add
          (List.repeat a n ++ ([R] ++ List.repeat c n))
          (List.repeat a n ++ List.repeat b m ++ [R] ++ List.repeat c (n + m)),
      rw ←List.append_assoc,
      have cnm : List.repeat c (n + m) = List.repeat c m ++ List.repeat c n,
      {
        rw add_comm,
        apply List.repeat_add,
      },
      rw cnm,
      have rebra : (List.repeat a n ++ List.repeat b m ++ [R] ++ (List.repeat c m ++ List.repeat c n)) =
                   (List.repeat a n ++ (List.repeat b m ++ [R] ++ List.repeat c m) ++ List.repeat c n),
      {
        simp only [List.append_assoc],
      },
      rw rebra,
      apply CF_deri_with_prefix_and_postfix,
      exact epoch_b m,
    },
    apply CF_deri_of_deri_tran obtain_sum,
    use (R_, []),
    split_ile,
    use (List.repeat a n ++ List.repeat b m),
    use List.repeat c (n + m),
    split,
    {
      refl,
    },
    unfold anbmcnm,
    rw List.map_append_append,
    rw List.append_nil,
    repeat {
      rw List.map_repeat,
    },
    refl,
  },
end
