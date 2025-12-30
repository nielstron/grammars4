import Grammars.Classes.ContextFree.Basics.Toolbox
import Grammars.Utilities.ListUtils


variable {T : Type}

def lift_symbol {N₀ N : Type} (lift_N : N₀ → N) : symbol T N₀ → symbol T N
| symbol.terminal t    => symbol.terminal t
| symbol.nonterminal n => symbol.nonterminal (lift_N n)

def sink_symbol {N₀ N : Type} (sink_N : N → Option N₀) : symbol T N → Option (symbol T N₀)
| symbol.terminal t    => some (symbol.terminal t)
| symbol.nonterminal n => Option.map symbol.nonterminal (sink_N n)

def lift_string {N₀ N : Type} (lift_N : N₀ → N) :
  List (symbol T N₀) → List (symbol T N) :=
List.map (lift_symbol lift_N)

def sink_string {N₀ N : Type} (sink_N : N → Option N₀) :
  List (symbol T N) → List (symbol T N₀) :=
List.filterMap (sink_symbol sink_N)

def lift_rule {N₀ N : Type} (lift_N : N₀ → N) :
  N₀ × (List (symbol T N₀)) → N × (List (symbol T N)) :=
fun r => (lift_N r.fst, lift_string lift_N r.snd)

structure lifted_grammar (T : Type) where
  g₀ : CF_grammar T
  g : CF_grammar T
  lift_nt : g₀.nt → g.nt
  lift_inj : Function.Injective lift_nt
  corresponding_rules :
    ∀ r : g₀.nt × List (symbol T g₀.nt),
      r ∈ g₀.rules → lift_rule lift_nt r ∈ g.rules
  sink_nt : g.nt → Option g₀.nt
  sink_inj : ∀ x y, sink_nt x = sink_nt y → x = y ∨ sink_nt x = none
  preimage_of_rules :
    ∀ r : g.nt × List (symbol T g.nt),
      (r ∈ g.rules ∧ ∃ n₀ : g₀.nt, lift_nt n₀ = r.fst) →
        (∃ r₀ ∈ g₀.rules, lift_rule lift_nt r₀ = r)
  lift_nt_sink : ∀ n₀ : g₀.nt, sink_nt (lift_nt n₀) = some n₀

private lemma lifted_grammar_inverse (lg : lifted_grammar T) :
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


private lemma lift_tran {lg : lifted_grammar T} {w₁ w₂ : List (symbol T lg.g₀.nt)}
    (hyp : CF_transforms lg.g₀ w₁ w₂) :
  CF_transforms lg.g (lift_string lg.lift_nt w₁) (lift_string lg.lift_nt w₂) :=
by
  rcases hyp with ⟨r, u, v, rin, bef, aft⟩
  refine ⟨lift_rule lg.lift_nt r, lift_string lg.lift_nt u, lift_string lg.lift_nt v, ?_⟩
  refine And.intro ?_ ?_
  · exact lg.corresponding_rules r rin
  ·
    refine And.intro ?_ ?_
    ·
      have lift_bef := congrArg (lift_string lg.lift_nt) bef
      unfold lift_string at *
      rw [List.map_append_append] at lift_bef
      convert lift_bef
    ·
      have lift_aft := congrArg (lift_string lg.lift_nt) aft
      unfold lift_string at *
      rw [List.map_append_append] at lift_aft
      exact lift_aft

lemma lift_deri {lg : lifted_grammar T} {w₁ w₂ : List (symbol T lg.g₀.nt)}
    (hyp : CF_derives lg.g₀ w₁ w₂) :
  CF_derives lg.g (lift_string lg.lift_nt w₁) (lift_string lg.lift_nt w₂) :=
by
  induction hyp with
  | refl =>
      exact CF_deri_self
  | tail ass' step ih =>
      apply CF_deri_of_deri_tran
      · exact ih
      · exact lift_tran step


def good_letter {lg : lifted_grammar T} : symbol T lg.g.nt → Prop
| (symbol.terminal t)    => True
| (symbol.nonterminal n) => (∃ n₀ : lg.g₀.nt, lg.sink_nt n = some n₀)

def good_string {lg : lifted_grammar T} (s : List (symbol T lg.g.nt)) :=
∀ a ∈ s, good_letter a

private lemma sink_tran {lg : lifted_grammar T} {w₁ w₂ : List (symbol T lg.g.nt)}
    (hyp : CF_transforms lg.g w₁ w₂)
    (ok_input : good_string w₁) :
  CF_transforms lg.g₀ (sink_string lg.sink_nt w₁) (sink_string lg.sink_nt w₂) :=
by
  rcases hyp with ⟨r, u, v, rin, bef, aft⟩

  rcases lg.preimage_of_rules r (by
    refine And.intro ?_ ?_
    · exact rin
    ·
      rw [bef] at ok_input
      have good_matched_nonterminal : good_letter (symbol.nonterminal r.fst) := by
        apply ok_input
        simp [List.mem_append, List.mem_singleton]
      rcases good_matched_nonterminal with ⟨n₀, hn₀⟩
      refine ⟨n₀, ?_⟩
      have almost := congrArg (Option.map lg.lift_nt) hn₀
      rw [lifted_grammar_inverse lg r.fst ⟨n₀, hn₀⟩] at almost
      have almost' : r.fst = lg.lift_nt n₀ := by
        apply Option.some_injective
        simpa using almost
      exact almost'.symm
  ) with ⟨p, pin, preimage⟩

  have filterMap_lift :
      ∀ l : List (symbol T lg.g₀.nt),
        List.filterMap (sink_symbol lg.sink_nt) (List.map (lift_symbol lg.lift_nt) l) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
        cases a with
        | terminal t =>
            simp [lift_symbol, sink_symbol, ih]
        | nonterminal n =>
            simp [lift_symbol, sink_symbol, lg.lift_nt_sink, ih]

  refine ⟨p, sink_string lg.sink_nt u, sink_string lg.sink_nt v, ?_⟩
  refine And.intro ?_ ?_
  · exact pin
  ·
    refine And.intro ?_ ?_
    ·
      have sink_bef := congrArg (sink_string lg.sink_nt) bef
      unfold sink_string at *
      rw [List.filter_map_append_append] at sink_bef
      convert sink_bef
      rw [←preimage]
      unfold lift_rule
      dsimp only
      change
        [symbol.nonterminal p.fst] =
        List.filterMap (sink_symbol lg.sink_nt)
          (List.map (lift_symbol lg.lift_nt) [symbol.nonterminal p.fst])
      simp [lift_symbol, sink_symbol, lg.lift_nt_sink]
    ·
      have sink_aft := congrArg (sink_string lg.sink_nt) aft
      unfold sink_string at *
      rw [List.filter_map_append_append] at sink_aft
      convert sink_aft
      rw [←preimage]
      unfold lift_rule
      dsimp only
      unfold lift_string
      exact (filterMap_lift p.2).symm

lemma sink_deri (lg : lifted_grammar T) (w₁ w₂ : List (symbol T lg.g.nt))
    (hyp : CF_derives lg.g w₁ w₂)
    (ok_input : good_string w₁) :
  CF_derives lg.g₀ (sink_string lg.sink_nt w₁) (sink_string lg.sink_nt w₂)
  ∧ good_string w₂ :=
by
  induction hyp with
  | refl =>
      refine And.intro ?_ ?_
      · exact CF_deri_self
      · exact ok_input
  | tail ass' step ih =>
      rename_i b c
      refine And.intro ?_ ?_
      ·
        apply CF_deri_of_deri_tran
        · exact ih.left
        · exact sink_tran step ih.right
      ·
        intro a in_y
        have ihr := ih.right a
        rcases step with ⟨r, u, v, in_rules, bef, aft⟩
        rw [bef] at ihr
        rw [List.mem_append] at ihr
        rw [aft] at in_y
        rw [List.mem_append] at in_y
        cases in_y with
        | inl in_y =>
            rw [List.mem_append] at in_y
            cases in_y with
            | inl in_y =>
                apply ihr
                rw [List.mem_append]
                exact Or.inl (Or.inl in_y)
            | inr in_y =>
                have exn₀ : ∃ n₀ : lg.g₀.nt, lg.lift_nt n₀ = r.fst := by
                  by_cases h : lg.sink_nt r.fst = none
                  ·
                    exfalso
                    have ruu : symbol.nonterminal r.fst ∈ b := by
                      rw [bef]
                      simp [List.mem_append]
                    have glruf' : good_letter (symbol.nonterminal r.fst) :=
                      ih.right (symbol.nonterminal r.fst) ruu
                    have glruf : False := by
                      simpa [good_letter, h] using glruf'
                    exact glruf.elim
                  ·
                    rcases (Option.ne_none_iff_exists'.mp h) with ⟨x, ex⟩
                    refine ⟨x, ?_⟩
                    have gix := lifted_grammar_inverse lg r.fst ⟨x, ex⟩
                    rw [ex] at gix
                    have gix' : lg.lift_nt x = r.fst := by
                      apply Option.some_injective
                      simpa using gix
                    exact gix'
                rcases lg.preimage_of_rules r ⟨in_rules, exn₀⟩ with ⟨r₀, in0, lif⟩
                rw [←lif] at in_y
                unfold lift_rule at in_y
                dsimp only at in_y
                unfold lift_string at in_y
                rw [List.mem_map] at in_y
                rcases in_y with ⟨s, s_in_rulsnd, symbol_letter⟩
                rw [←symbol_letter]
                cases s with
                | terminal =>
                    unfold lift_symbol
                    simp [good_letter]
                | nonterminal s =>
                    unfold lift_symbol
                    unfold good_letter
                    refine ⟨s, ?_⟩
                    exact lg.lift_nt_sink s
        | inr in_y =>
            apply ihr
            exact Or.inr in_y

syntax (name := fiveStepTac) "five_steps" : tactic

macro "five_steps" : tactic =>
  `(tactic|
    (--
    apply congrFun
    apply congrArg
    ext1 x
    cases x
    all_goals rfl))


variable {g₁ g₂ : CF_grammar T}

/-- similar to `lift_symbol (Option.some ∘ sum.inl)` -/
def sTN_of_sTN₁ : (symbol T g₁.nt) → (symbol T (Option (g₁.nt ⊕ g₂.nt)))
| (symbol.terminal st) => (symbol.terminal st)
| (symbol.nonterminal snt) => (symbol.nonterminal (some (Sum.inl snt)))

/-- similar to `lift_symbol (Option.some ∘ sum.inr)` -/
def sTN_of_sTN₂ : (symbol T g₂.nt) → (symbol T (Option (g₁.nt ⊕ g₂.nt)))
| (symbol.terminal st) => (symbol.terminal st)
| (symbol.nonterminal snt) => (symbol.nonterminal (some (Sum.inr snt)))

/-- similar to `lift_string (Option.some ∘ sum.inl)` -/
def lsTN_of_lsTN₁ : List (symbol T g₁.nt) → List (symbol T (Option (g₁.nt ⊕ g₂.nt))) :=
List.map sTN_of_sTN₁

/-- similar to `lift_string (Option.some ∘ sum.inr)` -/
def lsTN_of_lsTN₂ : List (symbol T g₂.nt) → List (symbol T (Option (g₁.nt ⊕ g₂.nt))) :=
List.map sTN_of_sTN₂

/-- similar to `lift_rule (Option.some ∘ sum.inl)` -/
def rule_of_rule₁ (r : g₁.nt × (List (symbol T g₁.nt))) :
  ((Option (g₁.nt ⊕ g₂.nt)) × (List (symbol T (Option (g₁.nt ⊕ g₂.nt))))) :=
(some (Sum.inl (Prod.fst r)), lsTN_of_lsTN₁ (Prod.snd r))

/-- similar to `lift_rule (Option.some ∘ sum.inr)` -/
def rule_of_rule₂ (r : g₂.nt × (List (symbol T g₂.nt))) :
  ((Option (g₁.nt ⊕ g₂.nt)) × (List (symbol T (Option (g₁.nt ⊕ g₂.nt))))) :=
(some (Sum.inr (Prod.fst r)), lsTN_of_lsTN₂ (Prod.snd r))
