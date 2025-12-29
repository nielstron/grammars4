import Grammars.Classes.Unrestricted.Basics.Toolbox
import Grammars.Utilities.ListUtils


section functions_lift_sink

variable {T N₀ N : Type}

def lift_symbol_ (lift_N : N₀ → N) : symbol T N₀ → symbol T N
| (symbol.terminal t)    => symbol.terminal t
| (symbol.nonterminal n) => symbol.nonterminal (lift_N n)

def sink_symbol_ (sink_N : N → Option N₀) : symbol T N → Option (symbol T N₀)
| (symbol.terminal t)    => some (symbol.terminal t)
| (symbol.nonterminal n) => Option.map symbol.nonterminal (sink_N n)

def lift_string_ (lift_N : N₀ → N) : List (symbol T N₀) → List (symbol T N) :=
List.map (lift_symbol_ lift_N)

def sink_string_ (sink_N : N → Option N₀) : List (symbol T N) → List (symbol T N₀) :=
List.filterMap (sink_symbol_ sink_N)

def lift_rule_ (lift_N : N₀ → N) : grule T N₀ → grule T N :=
fun r : grule T N₀ => grule.mk
  (lift_string_ lift_N r.input_L)
  (lift_N r.input_N)
  (lift_string_ lift_N r.input_R)
  (lift_string_ lift_N r.output_string)

end functions_lift_sink


section lifting_conditions

structure lifted_grammar_ (T : Type) where
  g₀ : grammar T
  g : grammar T
  lift_nt : g₀.nt → g.nt
  sink_nt : g.nt → Option g₀.nt
  lift_inj : Function.Injective lift_nt
  sink_inj : ∀ x y, sink_nt x = sink_nt y →
    x = y  ∨  sink_nt x = none
  lift_nt_sink : ∀ n₀ : g₀.nt, sink_nt (lift_nt n₀) = some n₀
  corresponding_rules : ∀ r : grule T g₀.nt,
    r ∈ g₀.rules →
      lift_rule_ lift_nt r ∈ g.rules
  preimage_of_rules : ∀ r : grule T g.nt,
    (r ∈ g.rules ∧ ∃ n₀ : g₀.nt, lift_nt n₀ = r.input_N) →
      (∃ r₀ ∈ g₀.rules, lift_rule_ lift_nt r₀ = r)

private lemma lifted_grammar_inverse {T : Type} (lg : lifted_grammar_ T) :
  ∀ x : lg.g.nt,
    (∃ n₀, lg.sink_nt x = some n₀) →
      Option.map lg.lift_nt (lg.sink_nt x) = some x :=
by
  intro x hyp
  rcases hyp with ⟨valu, ass⟩
  have hx : lg.sink_nt x = lg.sink_nt (lg.lift_nt valu) := by
    rw [ass, lg.lift_nt_sink]
  have inje := lg.sink_inj x (lg.lift_nt valu) hx
  have hxlift : x = lg.lift_nt valu := by
    cases inje with
    | inl case_valu =>
        exact case_valu
    | inr case_none =>
        rw [ass] at case_none
        cases case_none
  rw [ass]
  simp [hxlift]

end lifting_conditions


section translating_derivations

variable {T : Type}

private lemma lift_tran_ {lg : lifted_grammar_ T} {w₁ w₂ : List (symbol T lg.g₀.nt)}
    (hyp : grammar_transforms lg.g₀ w₁ w₂) :
  grammar_transforms lg.g (lift_string_ lg.lift_nt w₁) (lift_string_ lg.lift_nt w₂) :=
by
  rcases hyp with ⟨r, rin, u, v, bef, aft⟩
  refine ⟨lift_rule_ lg.lift_nt r, ?_, ?_⟩
  · exact lg.corresponding_rules r rin
  ·
    refine ⟨lift_string_ lg.lift_nt u, lift_string_ lg.lift_nt v, ?_, ?_⟩
    ·
      have lift_bef := congrArg (lift_string_ lg.lift_nt) bef
      unfold lift_string_ at *
      rw [List.map_append_append, List.map_append_append] at lift_bef
      exact lift_bef
    ·
      have lift_aft := congrArg (lift_string_ lg.lift_nt) aft
      unfold lift_string_ at *
      rw [List.map_append_append] at lift_aft
      exact lift_aft

lemma lift_deri_ (lg : lifted_grammar_ T) {w₁ w₂ : List (symbol T lg.g₀.nt)}
    (hyp : grammar_derives lg.g₀ w₁ w₂) :
  grammar_derives lg.g (lift_string_ lg.lift_nt w₁) (lift_string_ lg.lift_nt w₂) :=
by
  induction hyp with
  | refl =>
      exact grammar_deri_self
  | tail _ step ih =>
      apply grammar_deri_of_deri_tran
      · exact ih
      · exact lift_tran_ step


def good_letter_ {lg : lifted_grammar_ T} : symbol T lg.g.nt → Prop
| (symbol.terminal t)    => True
| (symbol.nonterminal n) => (∃ n₀ : lg.g₀.nt, lg.sink_nt n = some n₀)

def good_string_ {lg : lifted_grammar_ T} (s : List (symbol T lg.g.nt)) :=
∀ a ∈ s, good_letter_ a

private lemma sink_tran_ {lg : lifted_grammar_ T} {w₁ w₂ : List (symbol T lg.g.nt)}
    (hyp : grammar_transforms lg.g w₁ w₂)
    (ok_input : good_string_ w₁) :
  grammar_transforms lg.g₀ (sink_string_ lg.sink_nt w₁) (sink_string_ lg.sink_nt w₂)
  ∧ good_string_ w₂ :=
by
  rcases hyp with ⟨r, rin, u, v, bef, aft⟩

  rcases lg.preimage_of_rules r (by
    refine And.intro ?_ ?_
    · exact rin
    ·
      rw [bef] at ok_input
      have good_matched_nonterminal : good_letter_ (symbol.nonterminal r.input_N) := by
        apply ok_input
        simp [List.mem_append]
      rcases good_matched_nonterminal with ⟨n₀, hn₀⟩
      refine ⟨n₀, ?_⟩
      have almost := congrArg (Option.map lg.lift_nt) hn₀
      rw [lifted_grammar_inverse lg r.input_N ⟨n₀, hn₀⟩] at almost
      have almost' : r.input_N = lg.lift_nt n₀ := by
        apply Option.some_injective
        simpa using almost
      exact almost'.symm
  ) with ⟨r₀, pre_in, preimage⟩
  cases preimage

  have filterMap_lift :
      ∀ l : List (symbol T lg.g₀.nt),
        List.filterMap (sink_symbol_ lg.sink_nt) (List.map (lift_symbol_ lg.lift_nt) l) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
        cases a with
        | terminal t =>
            simp [lift_symbol_, sink_symbol_, ih]
        | nonterminal n =>
            simp [lift_symbol_, sink_symbol_, lg.lift_nt_sink, ih]

  refine And.intro ?_ ?_
  ·
    refine ⟨r₀, pre_in, sink_string_ lg.sink_nt u, sink_string_ lg.sink_nt v, ?_, ?_⟩
    ·
      have sink_bef := congrArg (sink_string_ lg.sink_nt) bef
      unfold sink_string_ at *
      rw [List.filter_map_append_append, List.filter_map_append_append] at sink_bef
      simpa [lift_rule_, lift_string_, filterMap_lift, lift_symbol_, sink_symbol_, lg.lift_nt_sink] using sink_bef
    ·
      have sink_aft := congrArg (sink_string_ lg.sink_nt) aft
      unfold sink_string_ at *
      rw [List.filter_map_append_append] at sink_aft
      simpa [lift_rule_, lift_string_, filterMap_lift, lift_symbol_, sink_symbol_, lg.lift_nt_sink] using sink_aft
  ·
    rw [bef] at ok_input
    rw [aft]
    unfold good_string_ at ok_input ⊢
    rw [List.forall_mem_append_append] at ok_input ⊢
    rw [List.forall_mem_append_append] at ok_input
    refine And.intro ?_ ?_
    · exact ok_input.1.1
    ·
      refine And.intro ?_ ?_
      ·
        intro a a_in_ros
        unfold lift_rule_ at a_in_ros
        dsimp only at a_in_ros
        unfold lift_string_ at a_in_ros
        rw [List.mem_map] at a_in_ros
        rcases a_in_ros with ⟨s, _, a_from_s⟩
        rw [←a_from_s]
        cases s with
        | terminal t =>
            simp [good_letter_, lift_symbol_]
        | nonterminal s =>
            unfold lift_symbol_
            unfold good_letter_
            exact ⟨s, lg.lift_nt_sink s⟩
      · exact ok_input.2.2

private lemma sink_deri_aux {lg : lifted_grammar_ T} {w₁ w₂ : List (symbol T lg.g.nt)}
    (hyp : grammar_derives lg.g w₁ w₂)
    (ok_input : good_string_ w₁) :
  grammar_derives lg.g₀ (sink_string_ lg.sink_nt w₁) (sink_string_ lg.sink_nt w₂)
  ∧ good_string_ w₂ :=
by
  induction hyp with
  | refl =>
      refine And.intro ?_ ?_
      · exact grammar_deri_self
      · exact ok_input
  | tail _ step ih =>
      have both := sink_tran_ step ih.2
      refine And.intro ?_ ?_
      ·
        apply grammar_deri_of_deri_tran
        · exact ih.1
        · exact both.1
      · exact both.2

lemma sink_deri_ (lg : lifted_grammar_ T) {w₁ w₂ : List (symbol T lg.g.nt)}
    (hyp : grammar_derives lg.g w₁ w₂)
    (ok_input : good_string_ w₁) :
  grammar_derives lg.g₀ (sink_string_ lg.sink_nt w₁) (sink_string_ lg.sink_nt w₂) :=
by
  exact (sink_deri_aux hyp ok_input).1

end translating_derivations
