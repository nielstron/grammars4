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
  simpa [hfun] using (List.filterMap_some (l := stri))

private lemma in_concatenated_of_in_combined
    {g₁ g₂ : CF_grammar T}
    {w : List T}
    (hyp : w ∈ CF_language (combined_grammar g₁ g₂)) :
  w ∈ CF_language g₁ * CF_language g₂ :=
by
  rw [Language.mem_mul]
  change
    CF_derives
      (combined_grammar g₁ g₂)
      [symbol.nonterminal (combined_grammar g₁ g₂).initial]
      (List.map symbol.terminal w) at hyp

  have hcases :
      ∃ y,
        CF_transforms
          (combined_grammar g₁ g₂)
          [symbol.nonterminal (combined_grammar g₁ g₂).initial]
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
        ∃ u : List (symbol T g₁.nt), ∃ v : List (symbol T g₂.nt),
          (CF_derives g₁ [symbol.nonterminal g₁.initial] u ∧
            CF_derives g₂ [symbol.nonterminal g₂.initial] v)
            ∧ (lsTN_of_lsTN₁ u ++ lsTN_of_lsTN₂ v = x) := by
    intro x ass
    induction ass with
    | refl =>
        refine ⟨[symbol.nonterminal g₁.initial], [symbol.nonterminal g₂.initial], ?_, ?_⟩
        · constructor <;> apply CF_deri_self
        · rfl
    | tail ass' orig ih =>
        rcases orig with ⟨orig_rule, c, d, orig_in, bef, aft⟩
        rcases ih with ⟨u, v, ⟨ih₁, ih₂⟩, ih_concat⟩
        cases List.eq_or_mem_of_mem_cons orig_in with
        | inl orig_in =>
            subst orig_in
            exfalso
            rw [← ih_concat] at bef
            dsimp only at bef
            have init_nt_in_bef_right :
                symbol.nonterminal none ∈ c ++ [symbol.nonterminal none] ++ d := by
              apply List.mem_append_left
              apply List.mem_append_right
              apply List.mem_singleton_self
            have init_nt_notin_bef_left :
                symbol.nonterminal none ∉ lsTN_of_lsTN₁ u ++ lsTN_of_lsTN₂ v := by
              rw [List.mem_append]
              push_neg
              constructor
              ·
                rw [List.mem_iff_nth_le]
                push_neg
                unfold lsTN_of_lsTN₁
                intro n hn
                have hn' : n < u.length := by
                  simpa [List.length_map] using hn
                rw [List.nthLe_map]
                cases u.nthLe n hn' with
                | terminal t =>
                    intro h
                    cases h
                | nonterminal s =>
                    unfold sTN_of_sTN₁
                    intro h
                    cases h
              ·
                rw [List.mem_iff_nth_le]
                push_neg
                unfold lsTN_of_lsTN₂
                intro n hn
                have hn' : n < v.length := by
                  simpa [List.length_map] using hn
                rw [List.nthLe_map]
                cases v.nthLe n hn' with
                | terminal t =>
                    intro h
                    cases h
                | nonterminal s =>
                    unfold sTN_of_sTN₂
                    intro h
                    cases h
            rw [bef] at init_nt_notin_bef_left
            exact init_nt_notin_bef_left init_nt_in_bef_right
        | inr orig_in =>
            clear derivation w
            change orig_rule ∈
              (List.map rule_of_rule₁ g₁.rules ++ List.map rule_of_rule₂ g₂.rules) at orig_in
            rw [List.mem_append] at orig_in
            rcases orig_in with orig_in_left | orig_in_right
            ·
                rw [List.mem_map] at orig_in_left
                rcases orig_in_left with ⟨r₁, r₁_in, r₁_conv⟩
                rw [aft]
                rw [bef] at ih_concat
                clear bef aft
                rw [← r₁_conv] at ih_concat ⊢
                clear r₁_conv
                have part_for_u :=
                  congr_arg (List.take (@lsTN_of_lsTN₁ T g₁ g₂ u).length) ih_concat
                have part_for_v :=
                  congr_arg (List.drop (@lsTN_of_lsTN₁ T g₁ g₂ u).length) ih_concat
                rw [List.take_left] at part_for_u
                rw [List.drop_left] at part_for_v

                have h_len : (@lsTN_of_lsTN₁ T g₁ g₂ u).length > c.length := by
                  by_contra contra
                  push_neg at contra

                  have not_in : symbol.nonterminal (rule_of_rule₁ r₁).fst ∉ lsTN_of_lsTN₂ v := by
                    unfold lsTN_of_lsTN₂
                    rw [List.mem_map]
                    rintro ⟨s, -, imposs⟩
                    cases s with
                    | terminal t =>
                        cases imposs
                    | nonterminal s =>
                        have inr_eq_inl := Option.some.inj (symbol.nonterminal.inj imposs)
                        cases inr_eq_inl

                  have yes_in :
                      symbol.nonterminal (@rule_of_rule₁ T g₁ g₂ r₁).fst ∈ lsTN_of_lsTN₂ v := by
                    have lcth := congr_fun (congr_arg List.nth ih_concat) c.length
                    have clength :
                        List.nth
                          ((c : List (symbol T (Option (g₁.nt ⊕ g₂.nt)))) ++
                            [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++
                              (d : List (symbol T (Option (g₁.nt ⊕ g₂.nt))))) c.length =
                          some (symbol.nonterminal (@rule_of_rule₁ T g₁ g₂ r₁).fst) := by
                      have h : (c : List (symbol T (Option (g₁.nt ⊕ g₂.nt)))).length ≤ c.length := by
                        simpa using (le_rfl : c.length ≤ c.length)
                      calc
                        List.nth
                            ((c : List (symbol T (Option (g₁.nt ⊕ g₂.nt)))) ++
                              [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++
                                (d : List (symbol T (Option (g₁.nt ⊕ g₂.nt))))) c.length =
                            List.nth
                              ([symbol.nonterminal (rule_of_rule₁ r₁).fst] ++
                                (d : List (symbol T (Option (g₁.nt ⊕ g₂.nt)))))
                              (c.length - (c : List (symbol T (Option (g₁.nt ⊕ g₂.nt)))).length) := by
                          simpa using
                            (List.nth_append_right
                              (l₁ := (c : List (symbol T (Option (g₁.nt ⊕ g₂.nt)))))
                              (l₂ :=
                                [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++
                                  (d : List (symbol T (Option (g₁.nt ⊕ g₂.nt)))))
                              (n := c.length)
                              h)
                        _ = some (symbol.nonterminal (@rule_of_rule₁ T g₁ g₂ r₁).fst) := by
                          simp [List.nth]
                    have lcth_cast := lcth
                    have clength_combined :
                        List.nth
                          (c ++
                            [symbol.nonterminal
                                ((rule_of_rule₁ r₁).fst : (combined_grammar g₁ g₂).nt)] ++ d)
                            c.length =
                          some (symbol.nonterminal (@rule_of_rule₁ T g₁ g₂ r₁).fst) := by
                      simpa [combined_grammar] using clength
                    simp [clength_combined] at lcth_cast
                    rw [List.nth_append_right
                      (l₁ := lsTN_of_lsTN₁ u)
                      (l₂ := lsTN_of_lsTN₂ v)
                      (n := c.length)
                      contra] at lcth_cast
                    exact List.nth_mem lcth_cast

                  exact not_in yes_in

      -- nonterminal was rewritten in the left half of `a` ... upgrade `u`
      have d' : List (symbol T (combined_grammar g₁ g₂).nt) :=
        List.take ((@lsTN_of_lsTN₁ T g₁ g₂ u).length - (c.length + 1)) d
      have u' : List (symbol T g₁.nt) :=
        lsTN₁_of_lsTN (c ++ (rule_of_rule₁ r₁).snd ++ d')
      refine ⟨u', v, ?_, ?_⟩
      · refine ⟨?_, ih₂⟩
        change
          CF_derives g₁ [symbol.nonterminal g₁.initial]
            (lsTN₁_of_lsTN (
              c ++ (rule_of_rule₁ r₁).snd ++
                (List.take ((lsTN_of_lsTN₁ u).length - (c.length + 1)) d)
            ))
        apply CF_deri_of_deri_tran ih₁
        convert_to
          CF_transforms
            g₁
            (lsTN₁_of_lsTN (
              List.take (lsTN_of_lsTN₁ u).length (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++ d)
            ))
            (lsTN₁_of_lsTN (c ++ (rule_of_rule₁ r₁).snd ++ List.take ((lsTN_of_lsTN₁ u).length - (c.length + 1)) d))
        · rw [←part_for_u, self_of_lsTN₁]
        refine ⟨r₁, ?_, ?_⟩
        · exact r₁_in
        refine ⟨lsTN₁_of_lsTN c, lsTN₁_of_lsTN (List.take (u.length - (c.length + 1)) d), ?_⟩
        constructor
        ·
          convert_to
            lsTN₁_of_lsTN (
              c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++
                (List.take (u.length - (c.length + 1)) d)
            ) =
              lsTN₁_of_lsTN c ++ [symbol.nonterminal r₁.fst] ++
                lsTN₁_of_lsTN (List.take (u.length - (c.length + 1)) d)
          ·
            apply congr_arg
            have trivi_len : (lsTN_of_lsTN₁ u).length = u.length := by
              unfold lsTN_of_lsTN₁
              rw [List.length_map]
            rw [trivi_len]
            have another_trivi_len :
                c.length + 1 = (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length := by
              rw [List.length_append, List.length_singleton]
            rw [another_trivi_len]
            have borrow_and_return :
                u.length =
                  (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length +
                    (u.length - (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length) := by
              symmetry
              clear_except h_len
              apply Nat.add_sub_of_le
              rw [List.length_append, List.length_singleton]
              unfold lsTN_of_lsTN₁ at h_len
              rw [List.length_map] at h_len
              rw [Nat.succ_le_iff]
              exact h_len
            convert_to
              List.take
                ((c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length +
                  (u.length - (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length))
                (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++ d) =
                c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++
                  List.take (u.length - (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length) d
            ·
              apply congr_fun
              apply congr_arg
              exact borrow_and_return
            rw [List.take_append]
          unfold lsTN₁_of_lsTN
          rw [List.filterMap_append_append]
          rfl
        ·
          convert_to
            lsTN₁_of_lsTN (c ++ (rule_of_rule₁ r₁).snd ++ (List.take (u.length - (c.length + 1)) d)) =
              lsTN₁_of_lsTN c ++ r₁.snd ++ lsTN₁_of_lsTN (List.take (u.length - (c.length + 1)) d)
          ·
            apply congr_arg
            trim
            unfold lsTN_of_lsTN₁
            rw [List.length_map]
          unfold lsTN₁_of_lsTN
          rw [List.filterMap_append_append]
          change
            List.filterMap sTN₁_of_sTN c ++ lsTN₁_of_lsTN (lsTN_of_lsTN₁ r₁.snd) ++
              List.filterMap sTN₁_of_sTN (List.take (u.length - (c.length + 1)) d) =
              List.filterMap sTN₁_of_sTN c ++ r₁.snd ++
                List.filterMap sTN₁_of_sTN (List.take (u.length - (c.length + 1)) d)
          rw [self_of_lsTN₁]
      ·
        have trivi_min :
            min ((@lsTN_of_lsTN₁ T g₁ g₂ u).length - (c.length + 1)) d.length =
              (@lsTN_of_lsTN₁ T g₁ g₂ u).length - (c.length + 1) := by
          apply min_eq_left
          unfold lsTN_of_lsTN₁
          rw [List.length_map]
          clear_except part_for_u
          unfold lsTN_of_lsTN₁ at part_for_u
          have lengs := congr_arg List.length part_for_u
          rw [List.length_map] at lengs
          rw [List.length_take] at lengs
          rw [List.length_append] at lengs
          rw [List.length_append] at lengs
          rw [List.length_singleton] at lengs
          have uleng_le : u.length ≤ c.length + 1 + d.length := by
            rw [←min_eq_left_iff]
            exact lengs.symm
          clear_except uleng_le
          omega
        have c_converted_and_back :
            List.map sTN_of_sTN₁ (List.filterMap sTN₁_of_sTN c) = c := by
          /-
            Simplified schema of this conversion (applies to some other conversions, too):
            we have `g ∘ f = id` but `f ∘ g` does not annihilate (in general)
            we need `(f ∘ g)(c) = c` for a specific `c`
            which we can express as `c = f(x)` and then
            we calculate `f(g(c)) = f(g(f(x))) = f(x) = c` hooray!
          -/
          have taken_c_from_u := congr_arg (List.take c.length) part_for_u
          rw [List.take_take] at taken_c_from_u
          rw [min_eq_left (le_of_lt h_len)] at taken_c_from_u
          rw [List.append_assoc] at taken_c_from_u
          rw [List.take_left] at taken_c_from_u
          convert_to
            List.map sTN_of_sTN₁ (List.filterMap sTN₁_of_sTN (List.take c.length (lsTN_of_lsTN₁ u))) = c
          · rw [taken_c_from_u]
          unfold lsTN_of_lsTN₁
          rw [←List.map_take]
          change List.map sTN_of_sTN₁ (lsTN₁_of_lsTN (lsTN_of_lsTN₁ (List.take c.length u))) = _
          rw [self_of_lsTN₁]
          rw [List.map_take]
          exact taken_c_from_u
        have d_converted_and_back :
            List.map sTN_of_sTN₁ (List.filterMap sTN₁_of_sTN (List.take (
              (List.map (@sTN_of_sTN₁ T g₁ g₂) u).length - (c.length + 1)
            ) d)) =
              List.take ((List.map (@sTN_of_sTN₁ T g₁ g₂) u).length - (c.length + 1)) d := by
          have taken_d_from_dropped_u := congr_arg (List.drop (c.length + 1)) part_for_u
          have for_the_decomposition :
              (@lsTN_of_lsTN₁ T g₁ g₂ u).length =
                (c.length + 1) + ((@lsTN_of_lsTN₁ T g₁ g₂ u).length - (c.length + 1)) := by
            symmetry
            apply Nat.add_sub_of_le
            exact Nat.succ_le_of_lt h_len
          rw [for_the_decomposition] at taken_d_from_dropped_u
          rw [List.drop_take] at taken_d_from_dropped_u
          have translate_counts :
              c.length + 1 = (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length := by
            rw [List.length_append, List.length_singleton]
          rw [translate_counts] at taken_d_from_dropped_u
          rw [List.drop_left] at taken_d_from_dropped_u
          rw [←translate_counts] at taken_d_from_dropped_u
          change
            List.map sTN_of_sTN₁ (
              List.filterMap sTN₁_of_sTN (List.take ((@lsTN_of_lsTN₁ T g₁ g₂ u).length - (c.length + 1)) d)
            ) = _
          rw [←taken_d_from_dropped_u]
          change List.map sTN_of_sTN₁ (lsTN₁_of_lsTN (List.drop (c.length + 1) (List.map sTN_of_sTN₁ u))) = _
          rw [←List.map_drop]
          change List.map sTN_of_sTN₁ (lsTN₁_of_lsTN (lsTN_of_lsTN₁ (List.drop (c.length + 1) u))) = _
          rw [self_of_lsTN₁]
          rw [List.map_drop]
          exact taken_d_from_dropped_u
        have len_u' :
            u'.length =
              c.length + (@rule_of_rule₁ T g₁ g₂ r₁).snd.length + d'.length := by
          change
            (lsTN₁_of_lsTN (c ++ (rule_of_rule₁ r₁).snd ++ d')).length =
              c.length + (rule_of_rule₁ r₁).snd.length + d'.length
          unfold lsTN₁_of_lsTN
          rw [List.filterMap_append_append]
          convert_to
            (List.map sTN_of_sTN₁ (
              List.filterMap sTN₁_of_sTN c ++
              List.filterMap sTN₁_of_sTN (rule_of_rule₁ r₁).snd ++
              List.filterMap sTN₁_of_sTN d'
            )).length =
              c.length + (rule_of_rule₁ r₁).snd.length + d'.length
          · rw [List.length_map]
          rw [List.map_append_append]
          rw [c_converted_and_back]
          change
            (c ++ _ ++ List.map sTN_of_sTN₁ (List.filterMap sTN₁_of_sTN (
              List.take ((List.map (@sTN_of_sTN₁ T g₁ g₂) u).length - (c.length + 1)) d
            ))).length = _
          rw [d_converted_and_back]
          change (c ++ List.map sTN_of_sTN₁ (lsTN₁_of_lsTN (lsTN_of_lsTN₁ r₁.snd)) ++ d').length = _
          rw [self_of_lsTN₁]
          rw [List.length_append]
          rw [List.length_append]
          rfl
        have express_u'_as_crd :
            lsTN_of_lsTN₁ u' =
              List.take (@lsTN_of_lsTN₁ T g₁ g₂ u').length (c ++ (rule_of_rule₁ r₁).snd ++ d) := by
          change
            lsTN_of_lsTN₁ (lsTN₁_of_lsTN (c ++ (rule_of_rule₁ r₁).snd ++
              (List.take ((lsTN_of_lsTN₁ u).length - (c.length + 1)) d))) =
              List.take (lsTN_of_lsTN₁ u').length (c ++ (rule_of_rule₁ r₁).snd ++ d)
          convert_to
            c ++ (rule_of_rule₁ r₁).snd ++ (List.take ((lsTN_of_lsTN₁ u).length - (c.length + 1)) d) =
              List.take (lsTN_of_lsTN₁ u').length (c ++ (rule_of_rule₁ r₁).snd ++ d)
          ·
            unfold lsTN₁_of_lsTN
            rw [List.filterMap_append_append]
            unfold lsTN_of_lsTN₁
            rw [List.map_append_append]
            rw [c_converted_and_back]
            rw [d_converted_and_back]
            change c ++ List.map sTN_of_sTN₁ (lsTN₁_of_lsTN (lsTN_of_lsTN₁ r₁.snd)) ++ _ = _
            rw [self_of_lsTN₁]
            rfl
          have len_add_sub :
              (@lsTN_of_lsTN₁ T g₁ g₂ u').length =
                (c ++ (rule_of_rule₁ r₁).snd).length +
                  ((@lsTN_of_lsTN₁ T g₁ g₂ u').length - (c ++ (rule_of_rule₁ r₁).snd).length) := by
            symmetry
            apply Nat.add_sub_of_le
            unfold lsTN_of_lsTN₁
            rw [List.length_map]
            rw [len_u']
            rw [List.length_append]
            apply le_self_add
          rw [len_add_sub]
          rw [List.take_append]
          trim
          rw [List.length_append]
          apply congr_arg2 <;> rfl
        rw [express_u'_as_crd]
        have identity_of_suffixes :
            List.drop (@lsTN_of_lsTN₁ T g₁ g₂ u).length (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++ d) =
              List.drop (@lsTN_of_lsTN₁ T g₁ g₂ u').length (c ++ (rule_of_rule₁ r₁).snd ++ d) := by
          clear_except h_len trivi_min len_u'
          have h_len_ :
              (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length ≤ (@lsTN_of_lsTN₁ T g₁ g₂ u).length := by
            rw [List.length_append, List.length_singleton]
            apply Nat.succ_le_of_lt
            exact h_len
          have intermediate :
              List.drop (@lsTN_of_lsTN₁ T g₁ g₂ u).length (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++ d) =
                List.drop ((@lsTN_of_lsTN₁ T g₁ g₂ u).length - (c.length + 1)) d := by
            convert_to
              List.drop
                ((c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length +
                  ((lsTN_of_lsTN₁ u).length - (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst]).length))
                (c ++ [symbol.nonterminal (rule_of_rule₁ r₁).fst] ++ d) =
                List.drop ((lsTN_of_lsTN₁ u).length - (c.length + 1)) d
            ·
              symmetry
              apply congr_arg2 <;> try rfl
              apply Nat.add_sub_of_le
              exact h_len_
            rw [List.drop_append]
            apply congr_arg2 <;> try rfl
            rw [List.length_append, List.length_singleton]
                rw [intermediate]
                change _ = List.drop (List.map sTN_of_sTN₁ u').length (c ++ (rule_of_rule₁ r₁).snd ++ d)
                rw [List.length_map]
                rw [len_u']
                rw [← List.length_append]
                rw [List.drop_append]
                rw [List.length_take]
                rw [trivi_min]
                rw [part_for_v, identity_of_suffixes]
                apply List.take_append_drop
            ·
                rw [List.mem_map] at orig_in_right
                rcases orig_in_right with ⟨r₂, r₂_in, r₂_conv⟩
                rw [aft]
                rw [bef] at ih_concat
                clear bef aft a b
                rw [← r₂_conv] at ih_concat ⊢
                clear r₂_conv orig_rule
                have part_for_u :=
                  congr_arg (List.take (@lsTN_of_lsTN₁ T g₁ g₂ u).length) ih_concat
                have part_for_v :=
                  congr_arg (List.drop (@lsTN_of_lsTN₁ T g₁ g₂ u).length) ih_concat
                rw [List.take_left] at part_for_u
                rw [List.drop_left] at part_for_v

                have hlen_vd : (@lsTN_of_lsTN₂ T g₁ g₂ v).length > d.length := by
                  by_contra contra
                  push_neg at contra
                  have not_in : symbol.nonterminal (rule_of_rule₂ r₂).fst ∉ lsTN_of_lsTN₁ u := by
                    unfold lsTN_of_lsTN₁
                    rw [List.mem_map]
                    rintro ⟨s, -, imposs⟩
                    cases s with
                    | terminal t =>
                        cases imposs
                    | nonterminal s =>
                        have inl_eq_inr := Option.some.inj (symbol.nonterminal.inj imposs)
                        cases inl_eq_inr
                  have yes_in : symbol.nonterminal (rule_of_rule₂ r₂).fst ∈ lsTN_of_lsTN₁ u := by
                    have ih_backwards := congr_arg List.reverse ih_concat
                    repeat (rw [List.reverse_append] at ih_backwards)
                    have ldth := congr_fun (congr_arg List.nth ih_backwards) d.length
                    have dlengthth :
                        List.nth
                            (d.reverse ++
                              ([symbol.nonterminal (rule_of_rule₂ r₂).fst].reverse ++ c.reverse))
                            d.length =
                          some (symbol.nonterminal (rule_of_rule₂ r₂).fst) := by
                      have hlen : d.reverse.length ≤ d.length := by
                        simpa [List.length_reverse] using (le_rfl : d.length ≤ d.length)
                      calc
                        List.nth
                            (d.reverse ++
                              ([symbol.nonterminal (rule_of_rule₂ r₂).fst].reverse ++ c.reverse))
                            d.length =
                          List.nth
                              ([symbol.nonterminal (rule_of_rule₂ r₂).fst].reverse ++ c.reverse)
                              (d.length - d.reverse.length) := by
                            simpa using
                              (List.nth_append_right
                                (l₁ := d.reverse)
                                (l₂ :=
                                  [symbol.nonterminal (rule_of_rule₂ r₂).fst].reverse ++ c.reverse)
                                (n := d.length)
                                hlen)
                        _ = some (symbol.nonterminal (rule_of_rule₂ r₂).fst) := by
                          simp [List.length_reverse, List.nth]
                    rw [dlengthth] at ldth
                    have contra' : (List.reverse (@lsTN_of_lsTN₂ T g₁ g₂ v)).length ≤ d.length := by
                      simpa [List.length_reverse] using contra
                    rw [List.nth_append_right (l₁ := List.reverse (lsTN_of_lsTN₂ v))
                      (l₂ := List.reverse (lsTN_of_lsTN₁ u))
                      (n := d.length)
                      contra'] at ldth
                    have rrr := List.nth_mem ldth
                    simpa [List.mem_reverse] using rrr
                  exact not_in yes_in

                have total_length := congr_arg List.length ih_concat
                repeat (rw [List.length_append] at total_length)
                rw [List.length_singleton] at total_length
                have hlen_uc : (@lsTN_of_lsTN₁ T g₁ g₂ u).length ≤ c.length := by
                  by_contra too_long
                  push_neg at too_long
                  have imposs_gt_self : c.length + 1 + d.length > c.length + 1 + d.length := by
                    calc
                      c.length + 1 + d.length
                          = (@lsTN_of_lsTN₁ T g₁ g₂ u).length + (@lsTN_of_lsTN₂ T g₁ g₂ v).length := by
                            simpa using total_length.symm
                      _ > (@lsTN_of_lsTN₁ T g₁ g₂ u).length + d.length := by
                            exact add_lt_add_left hlen_vd _
                      _ ≥ c.length + d.length + 1 := by
                            apply Nat.succ_le_of_lt
                            exact add_lt_add_right too_long _
                      _ = c.length + 1 + d.length := by
                            exact Nat.add_right_comm _ _ _
                  exact (Nat.lt_irrefl _ imposs_gt_self)
                have hlen_uc_orig : u.length ≤ c.length := by
                  unfold lsTN_of_lsTN₁ at hlen_uc
                  rw [List.length_map] at hlen_uc
                  exact hlen_uc

                -- nonterminal was rewritten in the right half of `a` ... upgrade `v`
                let c' : List (symbol T (combined_grammar g₁ g₂).nt) :=
                  List.drop (@lsTN_of_lsTN₁ T g₁ g₂ u).length c
                let v' := lsTN₂_of_lsTN (c' ++ (rule_of_rule₂ r₂).snd ++ d)
                refine ⟨u, v', ?_, ?_⟩
                · refine ⟨ih₁, ?_⟩
                  change
                    CF_derives g₂ [symbol.nonterminal g₂.initial]
                      (@lsTN₂_of_lsTN T g₁ g₂
                        (List.drop (lsTN_of_lsTN₁ u).length c ++ (rule_of_rule₂ r₂).snd ++ d))
                  apply CF_deri_of_deri_tran ih₂
                  convert_to
                    CF_transforms
                      g₂
                      (lsTN₂_of_lsTN (
                        List.drop (lsTN_of_lsTN₁ u).length
                          (c ++ [symbol.nonterminal (rule_of_rule₂ r₂).fst] ++ d)))
                      (lsTN₂_of_lsTN
                        (List.drop (lsTN_of_lsTN₁ u).length c ++ (rule_of_rule₂ r₂).snd ++ d))
                  ·
                    rw [← part_for_v, self_of_lsTN₂]
                  refine ⟨r₂, r₂_in, ?_⟩
                  refine ⟨lsTN₂_of_lsTN c', lsTN₂_of_lsTN d, ?_⟩
                  constructor
                  ·
                    have eq_c' : List.drop u.length c = c' := by
                      change List.drop u.length c =
                        List.drop (List.map (@sTN_of_sTN₁ T g₁ g₂) u).length c
                      rw [List.length_map]
                    unfold lsTN_of_lsTN₁
                    rw [List.length_map]
                    unfold lsTN₂_of_lsTN
                    rw [List.append_assoc]
                    rw [List.drop_append_of_le_length hlen_uc_orig]
                    rw [← List.append_assoc]
                    rw [List.filterMap_append_append]
                    rw [eq_c']
                    rfl
                  ·
                    have eq_c' : List.drop u.length c = c' := by
                      change List.drop u.length c =
                        List.drop (List.map (@sTN_of_sTN₁ T g₁ g₂) u).length c
                      rw [List.length_map]
                    unfold lsTN_of_lsTN₁
                    rw [List.length_map]
                    unfold lsTN₂_of_lsTN
                    rw [List.filterMap_append_append]
                    change
                      List.filterMap sTN₂_of_sTN (List.drop u.length c) ++
                        lsTN₂_of_lsTN (lsTN_of_lsTN₂ r₂.snd) ++
                          List.filterMap sTN₂_of_sTN d =
                      List.filterMap sTN₂_of_sTN c' ++ r₂.snd ++
                        List.filterMap sTN₂_of_sTN d
                    rw [self_of_lsTN₂]
                    rw [eq_c']
                ·
                  have identity_of_prefixes :
                      List.take (@lsTN_of_lsTN₁ T g₁ g₂ u).length
                          (c ++ [symbol.nonterminal (rule_of_rule₂ r₂).fst] ++ d) =
                        List.take (@lsTN_of_lsTN₁ T g₁ g₂ u).length
                          (c ++ (rule_of_rule₂ r₂).snd ++ d) := by
                    -- both are equal to `List.take (@lsTN_of_lsTN₁ T g₁ g₂ u).length c`
                    repeat
                      (rw [List.append_assoc, List.take_append_of_le_length hlen_uc])
                  have express_v'_as_crd :
                      lsTN_of_lsTN₂ v' =
                        List.drop (@lsTN_of_lsTN₁ T g₁ g₂ u).length
                          (c ++ (rule_of_rule₂ r₂).snd ++ d) := by
                    change
                      List.map sTN_of_sTN₂
                          (List.filterMap sTN₂_of_sTN (
                            List.drop (lsTN_of_lsTN₁ u).length c ++ (rule_of_rule₂ r₂).snd ++ d)) =
                        List.drop (lsTN_of_lsTN₁ u).length (c ++ (rule_of_rule₂ r₂).snd ++ d)
                    rw [List.filterMap_append_append]
                    rw [List.map_append_append]
                    rw [List.append_assoc c]
                    rw [List.drop_append_of_le_length hlen_uc]
                    rw [← List.append_assoc]
                    apply congr_arg2 <;> apply congr_arg2
                    ·
                      have aux_plus_minus :
                          (lsTN_of_lsTN₁ u).length + (c.length - (lsTN_of_lsTN₁ u).length) = c.length := by
                        rw [← Nat.add_sub_assoc hlen_uc, Nat.add_sub_cancel_left]
                      have taken_c_from_v :=
                        congr_arg (List.take (c.length - (@lsTN_of_lsTN₁ T g₁ g₂ u).length)) part_for_v
                      rw [← List.drop_take] at taken_c_from_v
                      rw [List.append_assoc] at taken_c_from_v
                      rw [List.take_append_of_le_length (le_of_eq aux_plus_minus)] at taken_c_from_v
                      rw [aux_plus_minus] at taken_c_from_v
                      rw [List.take_length] at taken_c_from_v
                      rw [← taken_c_from_v]
                      unfold lsTN_of_lsTN₂
                      rw [← List.map_take]
                      change
                        lsTN_of_lsTN₂
                            (lsTN₂_of_lsTN
                              (lsTN_of_lsTN₂
                                (List.take (c.length - (lsTN_of_lsTN₁ u).length) v))) =
                          lsTN_of_lsTN₂ (List.take (c.length - (lsTN_of_lsTN₁ u).length) v)
                      rw [self_of_lsTN₂]
                    ·
                      unfold rule_of_rule₂
                      change
                        lsTN_of_lsTN₂ (lsTN₂_of_lsTN (lsTN_of_lsTN₂ r₂.snd)) =
                          lsTN_of_lsTN₂ r₂.snd
                      rw [self_of_lsTN₂]
                    ·
                      have taken_d_from_v :=
                        congr_arg (List.drop ((@lsTN_of_lsTN₂ T g₁ g₂ v).length - d.length)) part_for_v
                      rw [List.drop_drop] at taken_d_from_v
                      have dropped_exactly_length :
                          (@lsTN_of_lsTN₂ T g₁ g₂ v).length - d.length +
                              (@lsTN_of_lsTN₁ T g₁ g₂ u).length =
                            (c ++ [symbol.nonterminal (rule_of_rule₂ r₂).fst]).length := by
                        rw [List.length_append, List.length_singleton]
                        have reorder_sum :
                            (lsTN_of_lsTN₂ v).length - d.length + (lsTN_of_lsTN₁ u).length =
                              (lsTN_of_lsTN₁ u).length + (lsTN_of_lsTN₂ v).length - d.length := by
                          rw [Nat.add_sub_assoc]
                          apply Nat.add_comm
                          apply le_of_lt
                          exact hlen_vd
                        rw [reorder_sum, total_length]
                        apply Nat.add_sub_cancel
                      rw [dropped_exactly_length] at taken_d_from_v
                      rw [List.drop_left] at taken_d_from_v
                      rw [← taken_d_from_v]
                      unfold lsTN_of_lsTN₂
                      rw [← List.map_drop]
                      change
                        lsTN_of_lsTN₂
                            (lsTN₂_of_lsTN (lsTN_of_lsTN₂ (
                              List.drop ((List.map sTN_of_sTN₂ v).length - d.length) v))) =
                          lsTN_of_lsTN₂ (List.drop ((List.map sTN_of_sTN₂ v).length - d.length) v)
                      rw [self_of_lsTN₂]

                  rw [part_for_u, identity_of_prefixes, express_v'_as_crd]
                  apply List.take_append_drop
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
    rw List.filterMap_map,
    convert_to List.map symbol.terminal (List.filterMap some uₜ) = List.map symbol.terminal uₜ,
    rw List.filterMap_some,
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
    rw List.filterMap_map,
    convert_to List.map symbol.terminal (List.filterMap some vₜ) = List.map symbol.terminal vₜ,
    rw List.filterMap_some,
  },
  unfold liT_of_lsTN₃ at huvw,
  rw List.filterMap_append at huvw,
  unfold lsTN_of_lsTN₁ at huvw,
  unfold lsTN_of_lsTN₂ at huvw,
  repeat {
    rw List.filterMap_map at huvw,
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
  rw List.filterMap_some


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
