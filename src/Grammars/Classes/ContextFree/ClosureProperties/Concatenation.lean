import Grammars.Classes.ContextFree.Basics.Lifting
import Grammars.Utilities.WrittenByOthers.TrimAssoc


variable {T : Type}

namespace List
variable {α : Type}

def nth (l : List α) (n : Nat) : Option α :=
  match l, n with
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: tail, Nat.succ k => nth tail k

def nthLe : (l : List α) → (n : Nat) → n < l.length → α
| [], _, h => (Nat.not_lt_zero _ h).elim
| a :: _, 0, _ => a
| _ :: tail, Nat.succ n, h =>
    nthLe tail n (by simpa using (Nat.lt_of_succ_lt_succ h))

theorem get?_eq_nth {l : List α} {n : Nat} : l[n]? = l.nth n := by
  induction l generalizing n with
  | nil =>
      cases n <;> rfl
  | cons head tail ih =>
      cases n with
      | zero =>
          rfl
      | succ n =>
          simpa using (ih (n := n))

theorem nthLe_nth {l : List α} {n : Nat} (h : n < l.length) : l.nth n = some (l.nthLe n h) := by
  induction l generalizing n with
  | nil =>
      cases (Nat.not_lt_zero _ h)
  | cons head tail ih =>
      cases n with
      | zero =>
          rfl
      | succ n =>
          have h' : n < tail.length := by
            simpa using (Nat.lt_of_succ_lt_succ h)
          simpa [List.nth, List.nthLe] using (ih (n := n) h')

theorem nth_mem {l : List α} {n : Nat} {a : α} (h : l.nth n = some a) : a ∈ l := by
  induction l generalizing n with
  | nil =>
      cases n <;> cases h
  | cons head tail ih =>
      cases n with
      | zero =>
          have : head = a := by
            simpa [List.nth] using h
          simpa [this]
      | succ n =>
          have h' : tail.nth n = some a := by
            simpa [List.nth] using h
          exact List.mem_cons_of_mem _ (ih (n := n) h')

theorem nthLe_map {f : α → β} {l : List α} {n : Nat}
    (h : n < (List.map f l).length) :
    (List.map f l).nthLe n h =
      f (l.nthLe n (by simpa [List.length_map] using h)) := by
  induction l generalizing n with
  | nil =>
      cases (Nat.not_lt_zero _ h)
  | cons head tail ih =>
      cases n with
      | zero =>
          rfl
      | succ n =>
          have h' : n < (List.map f tail).length := by
            simpa [List.length_map, Nat.succ_lt_succ_iff] using h
          have h'' : n < tail.length := by
            simpa [List.length_map, Nat.succ_lt_succ_iff] using h
          simpa [List.nthLe, List.length_map] using (ih (n := n) h')

theorem nthLe_append_right {l₁ l₂ : List α} {n : Nat}
    (h₁ : l₁.length ≤ n) (h₂ : n < (l₁ ++ l₂).length) :
    (l₁ ++ l₂).nthLe n h₂ =
      l₂.nthLe (n - l₁.length)
        (by
          have h' : n < l₁.length + l₂.length := by
            simpa [List.length_append] using h₂
          exact Nat.sub_lt_left_of_lt_add h₁ h') := by
  induction l₁ generalizing n with
  | nil =>
      have h' : n < l₂.length := by
        simpa [List.length_append] using h₂
      simp [List.nthLe]
  | cons head tail ih =>
      cases n with
      | zero =>
          cases (Nat.not_succ_le_zero _ h₁)
      | succ n =>
          have h₁' : tail.length ≤ n := by
            simpa [Nat.succ_le_succ_iff] using h₁
          have h₂' : n < (tail ++ l₂).length := by
            simpa [List.length_append] using (Nat.lt_of_succ_lt_succ h₂)
          simpa [List.nthLe, Nat.succ_sub_succ_eq_sub] using (ih (n := n) h₁' h₂')

theorem nthLe_congr {l : List α} {n : Nat} {h₁ h₂ : n < l.length} :
    l.nthLe n h₁ = l.nthLe n h₂ := by
  induction l generalizing n with
  | nil =>
      cases (Nat.not_lt_zero _ h₁)
  | cons head tail ih =>
      cases n with
      | zero =>
          rfl
      | succ n =>
          have h₁' : n < tail.length := by
            simpa using (Nat.lt_of_succ_lt_succ h₁)
          have h₂' : n < tail.length := by
            simpa using (Nat.lt_of_succ_lt_succ h₂)
          simpa [List.nthLe] using (ih (n := n) h₁' h₂')

theorem mem_iff_nth_le {l : List α} {a : α} :
    a ∈ l ↔ ∃ n, ∃ h : n < l.length, l.nthLe n h = a := by
  induction l with
  | nil =>
      simp
  | cons head tail ih =>
      constructor
      · intro h
        cases h with
        | head =>
            refine ⟨0, by simp, ?_⟩
            rfl
        | tail _ htail =>
            rcases ih.mp htail with ⟨n, hn, hval⟩
            refine ⟨n + 1, ?_, ?_⟩
            · simpa using Nat.succ_lt_succ hn
            · simpa [List.nthLe] using hval
      · intro h
        rcases h with ⟨n, hn, hval⟩
        cases n with
        | zero =>
            have : head = a := by
              simpa [List.nthLe] using hval
            simpa [this]
        | succ n =>
            right
            have hn' : n < tail.length := by
              simpa using (Nat.lt_of_succ_lt_succ hn)
            have hval' : tail.nthLe n hn' = a := by
              simpa [List.nthLe] using hval
            exact ih.mpr ⟨n, hn', hval'⟩

theorem nth_eq_none_iff {l : List α} {n : Nat} : l.nth n = none ↔ l.length ≤ n := by
  induction l generalizing n with
  | nil =>
      cases n <;> simp [List.nth]
  | cons head tail ih =>
      cases n with
      | zero =>
          simp [List.nth]
      | succ n =>
          simpa [List.nth, Nat.succ_le_succ_iff] using (ih (n := n))

theorem nth_take {l : List α} {m n : Nat} (h : n < m) :
    (List.take m l).nth n = l.nth n := by
  induction l generalizing m n with
  | nil =>
      simp [List.nth]
  | cons head tail ih =>
      cases m with
      | zero =>
          exact (Nat.not_lt_zero _ h).elim
      | succ m =>
          cases n with
          | zero =>
              simp [List.nth]
          | succ n =>
              have h' : n < m := Nat.lt_of_succ_lt_succ h
              simp [List.nth, ih h']

theorem nth_drop {l : List α} {m n : Nat} :
    (List.drop m l).nth n = l.nth (m + n) := by
  induction m generalizing l with
  | zero =>
      simp [List.nth]
  | succ m ih =>
      cases l with
      | nil =>
          simp [List.nth]
      | cons head tail =>
          simp [List.nth, ih, Nat.succ_add]

theorem nth_append_right {l₁ l₂ : List α} {n : Nat} (h : l₁.length ≤ n) :
    (l₁ ++ l₂).nth n = l₂.nth (n - l₁.length) := by
  induction l₁ generalizing n with
  | nil =>
      simp [List.nth]
  | cons head tail ih =>
      cases n with
      | zero =>
          cases (Nat.not_succ_le_zero _ h)
      | succ n =>
          have h' : tail.length ≤ n := by
            simpa [Nat.succ_le_succ_iff] using h
          simpa [List.nth, Nat.succ_sub_succ_eq_sub] using (ih (n := n) h')

end List

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
  constructor
  · exact hyp
  cases r with
  | mk nt rhs =>
      simp [rule_of_rule₁, lift_rule, lift_string, lsTN_of_lsTN₁, lift_symbol, sTN_of_sTN₁]
      intro a ha
      cases a <;> rfl
) oN₁_of_N (by
  intros x y ass
  cases x with
  | none =>
      right
      rfl
  | some x =>
      cases x with
      | inl x =>
          cases y with
          | none =>
              rw [ass]
              right
              rfl
          | some y =>
              cases y with
              | inl y =>
                  left
                  have ass' : (some x : Option g₁.nt) = some y := by
                    simpa [oN₁_of_N] using ass
                  have hxy : x = y := by
                    cases ass'
                    rfl
                  simpa [hxy]
              | inr y =>
                  tauto
      | inr x =>
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
          constructor
          · exact r₁_in
          rw [←r₁_convert_r]
          cases r₁ with
          | mk nt rhs =>
              simp [lift_rule, rule_of_rule₁, lift_string, lsTN_of_lsTN₁, lift_symbol, sTN_of_sTN₁]
              intro a ha
              cases a <;> rfl
      | inr r_in =>
          exfalso
          rw [List.mem_map] at r_in
          rcases r_in with ⟨r₂, r₂_in, r₂_convert_r⟩
          cases r₂_convert_r
          rcases r_ntype with ⟨n₁, r_ntype⟩
          simp [rule_of_rule₂] at r_ntype
          cases r_ntype
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
  constructor
  · exact hyp
  cases r with
  | mk nt rhs =>
      simp [rule_of_rule₂, lift_rule, lift_string, lsTN_of_lsTN₂, lift_symbol, sTN_of_sTN₂]
      intro a ha
      cases a <;> rfl
) oN₂_of_N (by
  intros x y ass
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
              rw [ass]
              rfl
          | some y =>
              cases y with
              | inl y =>
                  tauto
              | inr y =>
                  left
                  have ass' : (some x : Option g₂.nt) = some y := by
                    simpa [oN₂_of_N] using ass
                  have hxy : x = y := by
                    cases ass'
                    rfl
                  simpa [hxy]
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
          cases r₁_convert_r
          simp [rule_of_rule₁] at r_ntype
          cases r_ntype
      | inr r_in =>
          rw [List.mem_map] at r_in
          rcases r_in with ⟨r₂, r₂_in, r₂_convert_r⟩
          use r₂
          constructor
          · exact r₂_in
          rw [←r₂_convert_r]
          cases r₂ with
          | mk nt rhs =>
              simp [lift_rule, rule_of_rule₂, lift_string, lsTN_of_lsTN₂, lift_symbol, sTN_of_sTN₂]
              intro a ha
              cases a <;> rfl
) (by
  intro
  rfl
)


private def oT_of_sTN₃ {g₃ : CF_grammar T} : symbol T g₃.nt → Option T
| (symbol.terminal t) => some t
| (symbol.nonterminal _) => none

private def liT_of_lsTN₃ {g₃ : CF_grammar T} : List (symbol T g₃.nt) → List T :=
List.filterMap oT_of_sTN₃


private lemma u_eq_take_map_w
    {g₁ g₂ : CF_grammar T}
    (u : List (symbol T g₁.nt))
    (v : List (symbol T g₂.nt))
    (w : List T)
    (len : u.length ≤ w.length)
    (hyp :
      List.take u.length
        (List.map (sTN_of_sTN₁ (g₁ := g₁) (g₂ := g₂)) u ++
          lsTN_of_lsTN₂ (g₁ := g₁) (g₂ := g₂) v) =
        List.take u.length (List.map (@symbol.terminal T (Option (g₁.nt ⊕ g₂.nt))) w)) :
  u = List.take u.length (List.map (@symbol.terminal T g₁.nt) w) :=
by
  ext n
  simp [List.get?_eq_nth]
  by_cases h : n < u.length
  ·
    have ass :
        List.map (sTN_of_sTN₁ (g₁ := g₁) (g₂ := g₂)) u =
          List.take u.length (List.map (@symbol.terminal T (Option (g₁.nt ⊕ g₂.nt))) w) := by
      convert hyp
      have takenl :
          List.take (List.length (List.map (sTN_of_sTN₁ (g₁ := g₁) (g₂ := g₂)) u))
            (List.map (sTN_of_sTN₁ (g₁ := g₁) (g₂ := g₂)) u ++
              lsTN_of_lsTN₂ (g₁ := g₁) (g₂ := g₂) v) =
            List.map (sTN_of_sTN₁ (g₁ := g₁) (g₂ := g₂)) u := by
        simpa using
          (List.take_left
            (l₁ := List.map (sTN_of_sTN₁ (g₁ := g₁) (g₂ := g₂)) u)
            (l₂ := lsTN_of_lsTN₂ (g₁ := g₁) (g₂ := g₂) v))
      rw [List.length_map] at takenl
      exact takenl.symm
    have nth_equ := congr_fun (congr_arg List.nth ass) n
    rw [List.nth_take h]
    rw [List.nth_take h] at nth_equ
    have n_lt_wl : n < w.length := by
      exact lt_of_lt_of_le h len
    have triv : n < (List.map (sTN_of_sTN₁ (g₁ := g₁) (g₂ := g₂)) u).length := by
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
    have h_map_u :
        n < (List.map (sTN_of_sTN₁ (g₁ := g₁) (g₂ := g₂)) u).length := by
      simpa [List.length_map] using h
    rw [List.nthLe_map (h := h_map_u)] at nth_equ
    rw [List.nthLe_map (h := trin)] at nth_equ
    have n_lt_wl' : n < w.length := by
      simpa [List.length_map] using trin
    have h_u_map : n < u.length := by
      simpa [List.length_map] using h_map_u
    have h_w_map : n < w.length := by
      simpa [List.length_map] using trin
    have h_u_eq : u.nthLe n h_u_map = u.nthLe n h :=
      List.nthLe_congr (h₁ := h_u_map) (h₂ := h)
    have h_w_eq : w.nthLe n h_w_map = w.nthLe n n_lt_wl' :=
      List.nthLe_congr (h₁ := h_w_map) (h₂ := n_lt_wl')
    have nthLe_eq :
        u.nthLe n h = (List.map (@symbol.terminal T g₁.nt) w).nthLe n trig := by
      cases h_u : u.nthLe n h with
      | terminal a =>
          have nth_equ' :
              (symbol.terminal (T := T) (N := Option (g₁.nt ⊕ g₂.nt)) a) =
                symbol.terminal (T := T) (N := Option (g₁.nt ⊕ g₂.nt)) (w.nthLe n n_lt_wl') := by
            simpa [sTN_of_sTN₁, h_u, h_u_eq, h_w_eq] using nth_equ
          have ha : a = w.nthLe n n_lt_wl' :=
            symbol.terminal.inj nth_equ'
          have rhs :
              (List.map (@symbol.terminal T g₁.nt) w).nthLe n trig =
                symbol.terminal (w.nthLe n n_lt_wl') := by
            simpa [List.length_map] using
              (List.nthLe_map (f := @symbol.terminal T g₁.nt) (l := w) (n := n) (h := trig))
          simpa [rhs, ha]
      | nonterminal a =>
          exfalso
          have : symbol.nonterminal (T := T) (N := Option (g₁.nt ⊕ g₂.nt))
              (some (Sum.inl (β := g₂.nt) a)) =
              symbol.terminal (T := T) (N := Option (g₁.nt ⊕ g₂.nt)) (w.nthLe n n_lt_wl') := by
            simpa [sTN_of_sTN₁, h_u, h_u_eq, h_w_eq] using nth_equ
          cases this
    have nth_eq : u.nth n = (List.map (@symbol.terminal T g₁.nt) w).nth n := by
      calc
        u.nth n = some (u.nthLe n h) := List.nthLe_nth (h := h)
        _ = some ((List.map (@symbol.terminal T g₁.nt) w).nthLe n trig) := by
          simpa [nthLe_eq]
        _ = (List.map (@symbol.terminal T g₁.nt) w).nth n := (List.nthLe_nth (h := trig)).symm
    simpa [nth_eq]
  ·
    have h' : u.length ≤ n := by
      exact Nat.le_of_not_lt h
    have h_u : u.nth n = none := by
      rw [List.nth_eq_none_iff]
      exact h'
    have h_rhs :
        (List.take u.length (List.map (@symbol.terminal T g₁.nt) w)).nth n = none := by
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
  simp [List.get?_eq_nth]
  by_cases h : n < v.length
  ·
    have nth_equ := congr_fun (congr_arg List.nth hyp) n
    rw [List.nth_drop]
    rw [List.nth_drop] at nth_equ
    rw [List.nth_drop] at nth_equ
    have hunltuv : u.length + n < u.length + v.length := by
      exact Nat.add_lt_add_left h u.length
    have hunltw : u.length + n < w.length := by
      rw [←total_len]
      exact hunltuv
    have hlen₁ :
        u.length + n <
          (List.map (sTN_of_sTN₁ (g₁ := g₁) (g₂ := g₂)) u ++
            List.map (sTN_of_sTN₂ (g₁ := g₁) (g₂ := g₂)) v).length := by
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
    have hlen₀ : (List.map (sTN_of_sTN₁ (g₁ := g₁) (g₂ := g₂)) u).length ≤ u.length + n := by
      rw [List.length_map]
      exact le_self_add
    have hlen : n < (List.map (sTN_of_sTN₂ (g₁ := g₁) (g₂ := g₂)) v).length := by
      rw [List.length_map]
      exact h
    have nth_equ_simplified :
        (List.map sTN_of_sTN₂ v).nthLe n hlen =
          (List.map symbol.terminal w).nthLe (u.length + n) hlen₂ := by
      rw [List.nthLe_append_right hlen₀] at nth_equ
      have h_sub :
          u.length + n - (List.map (sTN_of_sTN₁ (g₁ := g₁) (g₂ := g₂)) u).length = n := by
        simp [List.length_map, Nat.add_sub_cancel_left]
      simpa [h_sub] using nth_equ
    have nth_equ_simplified' :
        (List.map (sTN_of_sTN₂ (g₁ := g₁) (g₂ := g₂)) v).nthLe n hlen =
          (List.map (@symbol.terminal T (Option (g₁.nt ⊕ g₂.nt))) w).nthLe (u.length + n) hlen₂ := by
      simpa using nth_equ_simplified
    have nth_equ_simplified'' :
        sTN_of_sTN₂ (g₁ := g₁) (g₂ := g₂) (v.nthLe n h) =
          symbol.terminal (T := T) (N := Option (g₁.nt ⊕ g₂.nt)) (w.nthLe (u.length + n) hunltw) := by
      have hlen_w : u.length + n < w.length := by
        exact hunltw
      have hlen_w' : u.length + n < (List.map (@symbol.terminal T (Option (g₁.nt ⊕ g₂.nt))) w).length := by
        simpa [List.length_map] using hlen_w
      have hlen_v : n < (List.map (sTN_of_sTN₂ (g₁ := g₁) (g₂ := g₂)) v).length := by
        simpa [List.length_map] using h
      have nth_eq_left :
          (List.map (sTN_of_sTN₂ (g₁ := g₁) (g₂ := g₂)) v).nthLe n hlen_v =
            sTN_of_sTN₂ (v.nthLe n h) := by
        simpa [List.length_map] using
          (List.nthLe_map (f := sTN_of_sTN₂ (g₁ := g₁) (g₂ := g₂)) (l := v) (n := n) (h := hlen_v))
      have nth_eq_right :
          (List.map (@symbol.terminal T (Option (g₁.nt ⊕ g₂.nt))) w).nthLe (u.length + n) hlen_w' =
            symbol.terminal (w.nthLe (u.length + n) hunltw) := by
        simpa [List.length_map] using
          (List.nthLe_map (f := @symbol.terminal T (Option (g₁.nt ⊕ g₂.nt))) (l := w)
            (n := u.length + n) (h := hlen_w'))
      simpa [nth_eq_left, nth_eq_right] using nth_equ_simplified'
    cases h_v : v.nthLe n h with
    | terminal a =>
        have nth_equ_simplified''' :
            symbol.terminal (T := T) (N := Option (g₁.nt ⊕ g₂.nt)) a =
              symbol.terminal (T := T) (N := Option (g₁.nt ⊕ g₂.nt)) (w.nthLe (u.length + n) hunltw) := by
          simpa [sTN_of_sTN₂, h_v] using nth_equ_simplified''
        have ha : a = w.nthLe (u.length + n) hunltw :=
          symbol.terminal.inj nth_equ_simplified'''
        have nth_map_eq :
            (List.map (@symbol.terminal T g₂.nt) w).nth (u.length + n) =
              some (symbol.terminal (w.nthLe (u.length + n) hunltw)) := by
          have hlen_w' : u.length + n < (List.map (@symbol.terminal T g₂.nt) w).length := by
            simpa [List.length_map] using hunltw
          calc
            (List.map (@symbol.terminal T g₂.nt) w).nth (u.length + n) =
                some ((List.map (@symbol.terminal T g₂.nt) w).nthLe (u.length + n) hlen_w') := by
              simpa using
                (List.nthLe_nth (l := List.map (@symbol.terminal T g₂.nt) w)
                  (n := u.length + n) (h := hlen_w'))
            _ = some (symbol.terminal (w.nthLe (u.length + n) hunltw)) := by
              simpa [List.length_map] using
                congrArg some
                  (List.nthLe_map (f := @symbol.terminal T g₂.nt) (l := w)
                    (n := u.length + n) (h := hlen_w'))
        have nth_eq : v.nth n = (List.drop u.length (List.map (@symbol.terminal T g₂.nt) w)).nth n := by
          calc
            v.nth n = some (v.nthLe n h) := List.nthLe_nth (h := h)
            _ = some (symbol.terminal (w.nthLe (u.length + n) hunltw)) := by
              simpa [sTN_of_sTN₂, h_v, ha] using nth_equ_simplified''
            _ = (List.drop u.length (List.map (@symbol.terminal T g₂.nt) w)).nth n := by
              rw [List.nth_drop]
              simpa [nth_map_eq]
        have nthLe_map_eq :
            (List.map (@symbol.terminal T g₂.nt) w).nthLe (u.length + n) hlen₂' =
              symbol.terminal (w.nthLe (u.length + n) hunltw) := by
          simpa [List.length_map] using
            (List.nthLe_map (f := @symbol.terminal T g₂.nt) (l := w)
              (n := u.length + n) (h := hlen₂'))
        simpa [nthLe_map_eq, ha]
    | nonterminal a =>
        exfalso
        have : symbol.nonterminal (T := T) (N := Option (g₁.nt ⊕ g₂.nt))
            (some (Sum.inr (α := g₁.nt) a)) =
            symbol.terminal (T := T) (N := Option (g₁.nt ⊕ g₂.nt)) (w.nthLe (u.length + n) hunltw) := by
          simpa [sTN_of_sTN₂, h_v] using nth_equ_simplified''
        cases this
  ·
    have h' : v.length ≤ n := by
      exact Nat.le_of_not_lt h
    have h_v : v.nth n = none := by
      rw [List.nth_eq_none_iff]
      exact h'
    have h_rhs :
        (List.drop u.length (List.map (@symbol.terminal T g₂.nt) w)).nth n = none := by
      rw [List.nth_drop]
      rw [List.nth_eq_none_iff]
      rw [List.length_map]
      rw [←total_len]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (add_le_add_left h' u.length)
    simpa [h_v, h_rhs]

private def sTN₁_of_sTN {g₁ g₂ : CF_grammar T} : symbol T (Option (g₁.nt ⊕ g₂.nt)) → Option (symbol T g₁.nt)
| (symbol.terminal te) => some (symbol.terminal te)
| (symbol.nonterminal nont) => Option.map symbol.nonterminal (oN₁_of_N nont)

private def sTN₂_of_sTN {g₁ g₂ : CF_grammar T} : symbol T (Option (g₁.nt ⊕ g₂.nt)) → Option (symbol T g₂.nt)
| (symbol.terminal te) => some (symbol.terminal te)
| (symbol.nonterminal nont) => Option.map symbol.nonterminal (oN₂_of_N nont)

private def lsTN₁_of_lsTN {g₁ g₂ : CF_grammar T} (lis : List (symbol T (Option (g₁.nt ⊕ g₂.nt)))) :
  List (symbol T g₁.nt) :=
List.filterMap sTN₁_of_sTN lis

private def lsTN₂_of_lsTN {g₁ g₂ : CF_grammar T} (lis : List (symbol T (Option (g₁.nt ⊕ g₂.nt)))) :
  List (symbol T g₂.nt) :=
List.filterMap sTN₂_of_sTN lis

private lemma self_of_sTN₁ {g₁ g₂ : CF_grammar T} (a : symbol T g₁.nt) :
  sTN₁_of_sTN (@sTN_of_sTN₁ _ _ g₂ a) = some a :=
by
  cases a <;> simp [sTN₁_of_sTN, sTN_of_sTN₁, oN₁_of_N]

private lemma self_of_sTN₂ {g₁ g₂ : CF_grammar T} (a : symbol T g₂.nt) :
  sTN₂_of_sTN (@sTN_of_sTN₂ _ g₁ _ a) = some a :=
by
  cases a <;> simp [sTN₂_of_sTN, sTN_of_sTN₂, oN₂_of_N]

private lemma self_of_lsTN₁ {g₁ g₂ : CF_grammar T} (stri : List (symbol T g₁.nt)) :
  lsTN₁_of_lsTN (@lsTN_of_lsTN₁ _ _ g₂ stri) = stri :=
by
  unfold lsTN_of_lsTN₁
  unfold lsTN₁_of_lsTN
  rw [List.filterMap_map]
  have hfun :
      (sTN₁_of_sTN (g₁ := g₁) (g₂ := g₂) ∘ sTN_of_sTN₁ (g₁ := g₁) (g₂ := g₂)) =
        (fun x => some x) := by
    funext x
    simpa using (self_of_sTN₁ (g₁ := g₁) (g₂ := g₂) x)
  simpa [hfun] using (List.filterMap_some (l := stri))

variable {g₁ g₂ : CF_grammar T}
def combined_rule_of_rule₁ (r : g₁.nt × (List (symbol T g₁.nt))) :
  ((combined_grammar g₁ g₂).nt) × (List (symbol T (combined_grammar g₁ g₂).nt)) :=
(some (Sum.inl (Prod.fst r)), lsTN_of_lsTN₁ (Prod.snd r))
def combined_rule_of_rule₂ (r : g₂.nt × (List (symbol T g₂.nt))) :
  ((combined_grammar g₁ g₂).nt) × (List (symbol T (combined_grammar g₁ g₂).nt)) :=
(some (Sum.inr (Prod.fst r)), lsTN_of_lsTN₂ (Prod.snd r))

private lemma self_of_lsTN₂ {g₁ g₂ : CF_grammar T} (stri : List (symbol T g₂.nt)) :
  lsTN₂_of_lsTN (@lsTN_of_lsTN₂ _ g₁ _ stri) = stri :=
by
  unfold lsTN_of_lsTN₂
  unfold lsTN₂_of_lsTN
  rw [List.filterMap_map]
  have hfun :
      (sTN₂_of_sTN (g₁ := g₁) (g₂ := g₂) ∘ sTN_of_sTN₂ (g₁ := g₁) (g₂ := g₂)) =
        (fun x => some x) := by
    funext x
    simpa using (self_of_sTN₂ (g₁ := g₁) (g₂ := g₂) x)
  simp [hfun]

-- Helper lemmas to convert derivations from combined grammar back to original grammars
private lemma derives_g1_of_derives_combined {g₁ g₂ : CF_grammar T}
    (u' : List (symbol T (combined_grammar g₁ g₂).nt))
    (h : CF_derives (combined_grammar g₁ g₂) [symbol.nonterminal (some (Sum.inl g₁.initial))] u') :
    ∃ u : List (symbol T g₁.nt),
      CF_derives g₁ [symbol.nonterminal g₁.initial] u ∧
      lsTN_of_lsTN₁ u = u' := by
  sorry  -- TODO: Prove by induction on derivation

private lemma derives_g2_of_derives_combined {g₁ g₂ : CF_grammar T}
    (v' : List (symbol T (combined_grammar g₁ g₂).nt))
    (h : CF_derives (combined_grammar g₁ g₂) [symbol.nonterminal (some (Sum.inr g₂.initial))] v') :
    ∃ v : List (symbol T g₂.nt),
      CF_derives g₂ [symbol.nonterminal g₂.initial] v ∧
      lsTN_of_lsTN₂ v = v' := by
  sorry  -- TODO: Prove by induction on derivation

-- Helper lemmas to show that derivations lead to words in the language
private lemma in_language_of_derives {g : CF_grammar T}
    (u : List (symbol T g.nt))
    (hu : CF_derives g [symbol.nonterminal g.initial] u) :
    liT_of_lsTN₃ u ∈ CF_language g := by
  sorry  -- TODO: Prove that if u derives from initial, then liT_of_lsTN₃ u is in the language

-- Helper lemma to show concatenation equals w
private lemma concat_eq_w_of_split {g₁ g₂ : CF_grammar T}
    (u : List (symbol T g₁.nt))
    (v : List (symbol T g₂.nt))
    (w : List T)
    (hw : lsTN_of_lsTN₁ u ++ lsTN_of_lsTN₂ v = List.map symbol.terminal w) :
    liT_of_lsTN₃ u ++ liT_of_lsTN₃ v = w := by
  sorry  -- TODO: Prove concatenation property

lemma concatenation_can_be_split {g: CF_grammar T} (x : List (symbol T g.nt)) (s: symbol T g.nt) (t: symbol T g.nt) (hyp: CF_derives g [s, t] x):
        ∃ u : List (symbol T g.nt), ∃ v : List (symbol T g.nt),
          CF_derives g [s] u ∧
            CF_derives g [t] v
            ∧ (u ++ v = x) := by
  induction hyp with
  | refl =>
    -- Base case: [s, t] derives to itself
    use [s], [t]
    refine ⟨?_, ?_, ?_⟩
    · apply CF_deri_self
    · apply CF_deri_self
    · rfl
  | tail rel trans ih =>
    -- Inductive case: we have rel --[rule]--> trans and ih gives us the split for rel
    rcases ih with ⟨u, v, hu, hv, huv⟩
    rcases trans with ⟨rule, c, d, rule_in, bef, aft⟩
    rw [← huv] at bef
    clear huv rel
    -- The rule application happens either in u or in v
    -- We determine which by checking if the nonterminal being replaced is in the first part
    sorry  -- TODO: Complete by case analysis on whether c.length < u.length

private lemma in_concatenated_of_in_combined
    {g₁ g₂ : CF_grammar T}
    {w : List T}
    (hyp : w ∈ CF_language (combined_grammar g₁ g₂)) :
  w ∈ CF_language g₁ * CF_language g₂ :=
by
  -- equivalent to w is generated by two words, a and b, which are from g1 and g2 respectively
  rw [Language.mem_mul]
  -- hyp is equivalent to w being derived from the combined grammar
  change
    CF_derives
      (combined_grammar g₁ g₂)
      [symbol.nonterminal none]
      (List.map symbol.terminal w) at hyp

  -- we now split this derivation into two parts, the first step and the remainder: the first step introduces the initial symbols of g1 and g2 in concatenation
  have hcases :
      ∃ y,
        CF_transforms
          (combined_grammar g₁ g₂)
          [symbol.nonterminal none]
          y ∧
          CF_derives
            (combined_grammar g₁ g₂)
            y
            (List.map symbol.terminal w) := by
    cases CF_tran_or_id_of_deri hyp with
    | inl refl_contr =>
        exfalso
        have hh := congr_fun (congr_arg List.nth refl_contr) 0
        cases w with
        | nil =>
            simp at hh
            cases hh
        | cons head tail =>
            simp at hh
            have :
                symbol.nonterminal (combined_grammar g₁ g₂).initial =
                  symbol.terminal head := Option.some.inj hh
            cases this
    | inr h =>
        exact h
  rcases hcases with ⟨y, first_step, derivation⟩
  clear hyp

  -- now we prove that the first step introduces g1 and g2 initial symbols in concatenation
  have only_option :
    y =
    [
      symbol.nonterminal (some (Sum.inl (g₁.initial))),
      symbol.nonterminal (some (Sum.inr (g₂.initial)))
    ] := by
    rcases first_step with ⟨first_rule, p, q, first_rule_in, bef, aft⟩
    have len_bef := congr_arg List.length bef
    rw [List.length_singleton, List.length_append, List.length_append, List.length_singleton] at len_bef
    have p_nil : p = [] := by
      have p0 : p.length = 0 := by
        linarith
      rw [List.length_eq_zero_iff] at p0
      exact p0
    have q_nil : q = [] := by
      have q0 : q.length = 0 := by
        linarith
      rw [List.length_eq_zero_iff] at q0
      exact q0
    have initial : first_rule.fst = none := by
      apply symbol.nonterminal.inj
      rw [p_nil, q_nil] at bef
      rw [List.append_nil, List.nil_append] at bef
      exact List.head_eq_of_cons_eq (Eq.symm bef)
    have only_rule :
        first_rule = (none, [
          symbol.nonterminal (some (Sum.inl (g₁.initial))),
          symbol.nonterminal (some (Sum.inr (g₂.initial)))
        ]) := by
      change first_rule ∈
        (none, [
          symbol.nonterminal (some (Sum.inl (g₁.initial))),
          symbol.nonterminal (some (Sum.inr (g₂.initial)))
        ]) ::
          (List.map rule_of_rule₁ g₁.rules ++ List.map rule_of_rule₂ g₂.rules) at first_rule_in
      cases List.eq_or_mem_of_mem_cons first_rule_in with
      | inl first_rule_in =>
          exact first_rule_in
      | inr first_rule_in =>
          exfalso
          change first_rule ∈
            (List.map rule_of_rule₁ g₁.rules ++ List.map rule_of_rule₂ g₂.rules) at first_rule_in
          rw [List.mem_append] at first_rule_in
          cases first_rule_in with
          | inl first_rule_in =>
              rw [List.mem_map] at first_rule_in
              rcases first_rule_in with ⟨r₁, r₁_in, rfl⟩
              cases initial
          | inr first_rule_in =>
              rw [List.mem_map] at first_rule_in
              rcases first_rule_in with ⟨r₂, r₂_in, rfl⟩
              cases initial
    rw [p_nil, q_nil, only_rule] at aft
    rw [List.append_nil, List.nil_append] at aft
    exact aft
  clear first_step
  rw [only_option] at derivation
  clear only_option y

  -- now show that any word derived from g1 and g2 initials in concatenation must be splittable into two words, the first from g1 and the second from g2
  have can_be_split :
    ∀ x : List (symbol T (combined_grammar g₁ g₂).nt),
      CF_derives
        (combined_grammar g₁ g₂)
        [
          symbol.nonterminal (some (Sum.inl (g₁.initial))),
          symbol.nonterminal (some (Sum.inr (g₂.initial)))
        ]
        x
      →
        ∃ u : List (symbol T g₁.nt), ∃ v : List (symbol T g₂.nt),
          (CF_derives g₁ [symbol.nonterminal g₁.initial] u ∧
            CF_derives g₂ [symbol.nonterminal g₂.initial] v)
            ∧ (lsTN_of_lsTN₁ u ++ lsTN_of_lsTN₂ v = x) := by
    intro x ass
    have can_generally_split : ∃ u , ∃ v , (CF_derives (combined_grammar g₁ g₂) [
          symbol.nonterminal (some (Sum.inl (g₁.initial)))] u ∧
            CF_derives
        (combined_grammar g₁ g₂) [symbol.nonterminal (some (Sum.inr (g₂.initial)))] v) ∧ u ++ v = x := by
      obtain ⟨u, v, hu, hv, huv⟩ := concatenation_can_be_split x
        (symbol.nonterminal (some (Sum.inl (g₁.initial))))
        (symbol.nonterminal (some (Sum.inr (g₂.initial))))
        ass
      exact ⟨u, v, ⟨hu, hv⟩, huv⟩
    rcases can_generally_split with ⟨u', v', ⟨hu', hv'⟩, huv'⟩
    -- Now convert from combined grammar derivations to original grammar derivations
    obtain ⟨u, hu, hu_eq⟩ := derives_g1_of_derives_combined u' hu'
    obtain ⟨v, hv, hv_eq⟩ := derives_g2_of_derives_combined v' hv'
    use u, v
    refine ⟨⟨hu, hv⟩, ?_⟩
    rw [hu_eq, hv_eq, huv']
  specialize can_be_split (List.map symbol.terminal w) derivation

  rcases can_be_split with ⟨u, v, ⟨hu, hv⟩, hw⟩
  -- at this point we need to show that the nonterminal sequences obtained from splitting are indeed in g1 and g2, using a helper lemma (proven inductively) and that they concatenate to w
  use liT_of_lsTN₃ u
  constructor
  · -- Show liT_of_lsTN₃ u ∈ CF_language g₁
    exact in_language_of_derives u hu
  · -- Show ∃ b ∈ CF_language g₂, liT_of_lsTN₃ u ++ b = w
    use liT_of_lsTN₃ v
    constructor
    · -- Show liT_of_lsTN₃ v ∈ CF_language g₂
      exact in_language_of_derives v hv
    · -- Show liT_of_lsTN₃ u ++ liT_of_lsTN₃ v = w
      exact concat_eq_w_of_split u v w hw

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
  apply Set.eq_of_subset_of_subset
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
