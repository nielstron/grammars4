import Grammars.Classes.Unrestricted.Basics.Lifting
import Grammars.Utilities.ListUtils


variable {T : Type}

def union_grammar (g₁ g₂ : grammar T) : grammar T :=
grammar.mk (Option (g₁.nt ⊕ g₂.nt)) none (
  ⟨ [], none, [], [symbol.nonterminal (some (Sum.inl (g₁.initial)))] ⟩ :: (
  ⟨ [], none, [], [symbol.nonterminal (some (Sum.inr (g₂.initial)))] ⟩ :: (
  (List.map (lift_rule_ (some ∘ Sum.inl)) g₁.rules) ++
  (List.map (lift_rule_ (some ∘ Sum.inr)) g₂.rules)
  )))


variable {g₁ g₂ : grammar T}

private def oN₁_of_N : (union_grammar g₁ g₂).nt → (Option g₁.nt)
| none               => none
| (some (Sum.inl n)) => some n
| (some (Sum.inr _)) => none

private def oN₂_of_N : (union_grammar g₁ g₂).nt → (Option g₂.nt)
| none               => none
| (some (Sum.inl _)) => none
| (some (Sum.inr n)) => some n


private def lg₁ : lifted_grammar_ T :=
lifted_grammar_.mk g₁ (union_grammar g₁ g₂) (Option.some ∘ Sum.inl) oN₁_of_N (by
  intro x y hyp
  apply Sum.inl_injective
  apply Option.some_injective
  exact hyp
) (by
  intro x y hyp
  cases x with
  | none =>
      right
      rfl
  | some x =>
      cases x with
      | inl x_nt =>
          cases y with
          | none =>
              rw [hyp]
              right
              rfl
          | some y =>
              cases y with
              | inl y_nt =>
                  left
                  simp only [oN₁_of_N] at hyp
                  have hxy : x_nt = y_nt := Option.some.inj hyp
                  exact congrArg (fun nt => some (Sum.inl nt)) hxy
              | inr _ =>
                  cases hyp
      | inr =>
          right
          rfl
) (by
  intro
  rfl
) (by
  intro r hyp
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  rw [List.mem_map]
  refine ⟨r, hyp, rfl⟩
) (by
  rintro r ⟨rin, n₀, rnt⟩
  have rin' := (List.mem_cons.1 rin)
  cases rin' with
  | inl rin_eq =>
      exfalso
      rw [rin_eq] at rnt
      cases rnt
  | inr rin_tail =>
      have rin'' := (List.mem_cons.1 rin_tail)
      cases rin'' with
      | inl rin_eq =>
          exfalso
          rw [rin_eq] at rnt
          cases rnt
      | inr rin_tail =>
          change r ∈ (
              List.map (lift_rule_ (some ∘ Sum.inl)) g₁.rules ++
              List.map (lift_rule_ (some ∘ Sum.inr)) g₂.rules
            ) at rin_tail
          rcases (List.mem_append.1 rin_tail) with rin_tail | rin_tail
          ·
            rcases (List.mem_map.1 rin_tail) with ⟨r₁, r₁_in, r₁_lift⟩
            exact ⟨r₁, r₁_in, r₁_lift⟩
          ·
            exfalso
            rcases (List.mem_map.1 rin_tail) with ⟨r₂, _r₂_in, r₂_lift⟩
            rw [←r₂_lift] at rnt
            unfold lift_rule_ at rnt
            dsimp only at rnt
            have rnti := Option.some.inj rnt
            cases rnti
)

private def lg₂ : lifted_grammar_ T :=
lifted_grammar_.mk g₂ (union_grammar g₁ g₂) (Option.some ∘ Sum.inr) oN₂_of_N (by
  intro x y hyp
  apply Sum.inr_injective
  apply Option.some_injective
  exact hyp
) (by
  intro x y hyp
  cases x with
  | none =>
      right
      rfl
  | some x =>
      cases x with
      | inl _ =>
          right
          rfl
      | inr x_nt =>
          cases y with
          | none =>
              right
              rw [hyp]
              rfl
          | some y =>
              cases y with
              | inl _ =>
                  cases hyp
              | inr y_nt =>
                  left
                  simp only [oN₂_of_N] at hyp
                  have hxy : x_nt = y_nt := Option.some.inj hyp
                  exact congrArg (fun nt => some (Sum.inr nt)) hxy
) (by
  intro
  rfl
) (by
  intro r hyp
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  rw [List.mem_map]
  refine ⟨r, hyp, rfl⟩
) (by
  rintro r ⟨rin, n₀, rnt⟩
  have rin' := (List.mem_cons.1 rin)
  cases rin' with
  | inl rin_eq =>
      exfalso
      rw [rin_eq] at rnt
      cases rnt
  | inr rin_tail =>
      have rin'' := (List.mem_cons.1 rin_tail)
      cases rin'' with
      | inl rin_eq =>
          exfalso
          rw [rin_eq] at rnt
          cases rnt
      | inr rin_tail =>
          change r ∈ (
              List.map (lift_rule_ (some ∘ Sum.inl)) g₁.rules ++
              List.map (lift_rule_ (some ∘ Sum.inr)) g₂.rules
            ) at rin_tail
          rcases (List.mem_append.1 rin_tail) with rin_tail | rin_tail
          ·
            exfalso
            rcases (List.mem_map.1 rin_tail) with ⟨r₁, _r₁_in, r₁_lift⟩
            rw [←r₁_lift] at rnt
            unfold lift_rule_ at rnt
            dsimp only at rnt
            have rnti := Option.some.inj rnt
            cases rnti
          ·
            rcases (List.mem_map.1 rin_tail) with ⟨r₂, r₂_in, r₂_lift⟩
            exact ⟨r₂, r₂_in, r₂_lift⟩
)


lemma in_L₁_or_L₂_of_in_union {w : List T} (ass : w ∈ grammar_language (union_grammar g₁ g₂)) :
  w ∈ grammar_language g₁  ∨  w ∈ grammar_language g₂  :=
by
  unfold grammar_language at ass ⊢
  change grammar_generates (union_grammar g₁ g₂) w at ass
  change grammar_generates g₁ w ∨ grammar_generates g₂ w
  unfold grammar_generates at ass ⊢
  have hyp := grammar_tran_or_id_of_deri (g := union_grammar g₁ g₂) ass
  clear ass
  cases hyp with
  | inl hyp =>
      exfalso
      have zeroth := congrArg List.head? hyp
      cases w with
      | nil =>
          simp at zeroth
      | cons head tail =>
          have nt_eq_ter : symbol.nonterminal (union_grammar g₁ g₂).initial = symbol.terminal head := by
            exact Option.some.inj (by simpa using zeroth)
          cases nt_eq_ter
  | inr hyp =>
      rcases hyp with ⟨i, ⟨r, rin, u, v, bef, aft⟩, deri⟩

      have uv_nil : u = [] ∧ v = [] := by
        have bef_len := congrArg List.length bef
        simp [List.length_append, List.length_singleton, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at bef_len
        have hu : u.length = 0 := by
          linarith
        have hv : v.length = 0 := by
          linarith
        have hu' : u = [] := by
          simpa [List.length_eq_zero_iff] using hu
        have hv' : v = [] := by
          simpa [List.length_eq_zero_iff] using hv
        exact ⟨hu', hv'⟩
      rw [uv_nil.1, List.nil_append, uv_nil.2, List.append_nil] at bef aft

      have same_nt : (union_grammar g₁ g₂).initial = r.input_N := by
        have elemeq :
            [@symbol.nonterminal T (union_grammar g₁ g₂).nt (union_grammar g₁ g₂).initial] =
              [@symbol.nonterminal T (union_grammar g₁ g₂).nt r.input_N] := by
          have bef_len := congr_arg List.length bef
          rw [List.length_append_append, List.length_singleton, List.length_singleton] at bef_len
          have rl_first_len : r.input_L.length = 0 := by
            linarith
          have rl_third_len : r.input_R.length = 0 := by
            linarith
          have rl_first : r.input_L = [] := by
            cases h : r.input_L with
            | nil => rfl
            | cons hd tl =>
                simp [h] at rl_first_len
          have rl_third : r.input_R = [] := by
            cases h : r.input_R with
            | nil => rfl
            | cons hd tl =>
                simp [h] at rl_third_len
          rw [rl_first, rl_third] at bef
          exact bef
        exact symbol.nonterminal.inj (List.head_eq_of_cons_eq elemeq)

      have rin' := (List.mem_cons.1 rin)
      cases rin' with
      | inl rin_eq =>
          rw [rin_eq] at aft
          dsimp only at aft
          rw [aft] at deri
          left

          have sinked := sink_deri_ lg₁ deri
          specialize sinked (by
            unfold good_string_
            simp only [List.mem_singleton, forall_eq]
            exact ⟨g₁.initial, rfl⟩
          )
          convert sinked

          unfold sink_string_
          rw [List.filterMap_map]
          convert_to List.map symbol.terminal w = List.filterMap (Option.some ∘ symbol.terminal) w
          rw [←List.filterMap_map]
          rw [List.filterMap_some]
      | inr rin_tail =>
          have rin'' := (List.mem_cons.1 rin_tail)
          cases rin'' with
          | inl rin_eq =>
              rw [rin_eq] at aft
              dsimp only at aft
              rw [aft] at deri
              right

              have sinked := sink_deri_ lg₂ deri
              specialize sinked (by
                unfold good_string_
                simp only [List.mem_singleton, forall_eq]
                exact ⟨g₂.initial, rfl⟩
              )
              convert sinked

              unfold sink_string_
              rw [List.filterMap_map]
              convert_to List.map symbol.terminal w = List.filterMap (Option.some ∘ symbol.terminal) w
              rw [←List.filterMap_map]
              rw [List.filterMap_some]
          | inr rin_tail =>
              exfalso

              change r ∈ (
                  List.map (lift_rule_ (some ∘ Sum.inl)) g₁.rules ++
                  List.map (lift_rule_ (some ∘ Sum.inr)) g₂.rules
                ) at rin_tail
              rcases (List.mem_append.1 rin_tail) with rin_tail | rin_tail
              ·
                rcases (List.mem_map.1 rin_tail) with ⟨ror, _rri, rli⟩
                rw [←rli] at same_nt
                simp [lift_rule_] at same_nt
                cases same_nt
              ·
                rcases (List.mem_map.1 rin_tail) with ⟨ror, _rri, rli⟩
                rw [←rli] at same_nt
                simp [lift_rule_] at same_nt
                cases same_nt


lemma in_union_of_in_L₁ {w : List T} (ass : w ∈ grammar_language g₁) :
  w ∈ grammar_language (union_grammar g₁ g₂) :=
by
  unfold grammar_language at ass ⊢
  change grammar_generates g₁ w at ass
  change grammar_generates (union_grammar g₁ g₂) w
  unfold grammar_generates at ass ⊢
  refine grammar_deri_of_tran_deri (g := union_grammar g₁ g₂)
    (v := [symbol.nonterminal (some (Sum.inl g₁.initial))]) ?_ ?_
  ·
    refine ⟨⟨ [], none, [], [symbol.nonterminal (some (Sum.inl (g₁.initial)))] ⟩, ?_, ?_⟩
    · simp [union_grammar]
    ·
      refine ⟨[], [], ?_, ?_⟩ <;> simp [union_grammar]
  ·
    have lifted := lift_deri_ (@lg₁ _ _ g₂) ass
    change
      grammar_derives lg₁.g
        (lift_string_ lg₁.lift_nt [symbol.nonterminal g₁.initial])
        (List.map (@symbol.terminal T (union_grammar g₁ g₂).nt) w)
    have equiv_out :
        lift_string_ lg₁.lift_nt (List.map (@symbol.terminal T g₁.nt) w) =
          List.map (@symbol.terminal T (union_grammar g₁ g₂).nt) w := by
      simp [lift_string_, lift_symbol_, List.map_map]
    rw [equiv_out] at lifted
    exact lifted

lemma in_union_of_in_L₂ {w : List T} (ass : w ∈ grammar_language g₂) :
  w ∈ grammar_language (union_grammar g₁ g₂) :=
by
  unfold grammar_language at ass ⊢
  change grammar_generates g₂ w at ass
  change grammar_generates (union_grammar g₁ g₂) w
  unfold grammar_generates at ass ⊢
  refine grammar_deri_of_tran_deri (g := union_grammar g₁ g₂)
    (v := [symbol.nonterminal (some (Sum.inr g₂.initial))]) ?_ ?_
  ·
    refine ⟨⟨ [], none, [], [symbol.nonterminal (some (Sum.inr (g₂.initial)))] ⟩, ?_, ?_⟩
    · simp [union_grammar]
    ·
      refine ⟨[], [], ?_, ?_⟩ <;> simp [union_grammar]
  ·
    have lifted := lift_deri_ (@lg₂ _ g₁ _) ass
    change
      grammar_derives lg₂.g
        (lift_string_ lg₂.lift_nt [symbol.nonterminal g₂.initial])
        (List.map (@symbol.terminal T (union_grammar g₁ g₂).nt) w)
    have equiv_out :
        lift_string_ lg₂.lift_nt (List.map (@symbol.terminal T g₂.nt) w) =
          List.map (@symbol.terminal T (union_grammar g₁ g₂).nt) w := by
      simp [lift_string_, lift_symbol_, List.map_map]
    rw [equiv_out] at lifted
    exact lifted


/-- The class of recursively-enumerable languages is closed under union. -/
theorem RE_of_RE_u_RE (L₁ : Language T) (L₂ : Language T) :
  is_RE L₁  ∧  is_RE L₂   →   is_RE (L₁ + L₂)   :=
by
  rintro ⟨⟨g₁, eq_L₁⟩, ⟨g₂, eq_L₂⟩⟩
  unfold is_RE
  use union_grammar g₁ g₂
  ext w
  constructor
  ·
    intro ass
    rw [Language.mem_add, ←eq_L₁, ←eq_L₂]
    exact in_L₁_or_L₂_of_in_union ass
  ·
    intro ass
    cases ass with
    | inl case₁ =>
        rw [←eq_L₁] at case₁
        exact in_union_of_in_L₁ case₁
    | inr case₂ =>
        rw [←eq_L₂] at case₂
        exact in_union_of_in_L₂ case₂
