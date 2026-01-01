import Mathlib.Tactic

open Lean Elab Tactic

macro "in_list_explicit" : tactic =>
  `(tactic|
    repeat
      first
        | (try (apply List.mem_cons_self))
        | (try (apply List.mem_cons_of_mem)))

macro "split_ile" : tactic =>
  `(tactic|
    refine And.intro ?_ ?_
    · in_list_explicit)

namespace List

variable {α β : Type*} {x y z : List α}

section list_append_append

lemma length_append_append :
  List.length (x ++ y ++ z) = x.length + y.length + z.length :=
by rw [List.length_append, List.length_append]

lemma map_append_append {f : α → β} :
  List.map f (x ++ y ++ z) = List.map f x ++ List.map f y ++ List.map f z :=
by rw [List.map_append, List.map_append]

lemma filter_map_append_append {f : α → Option β} :
  List.filterMap f (x ++ y ++ z) = List.filterMap f x ++ List.filterMap f y ++ List.filterMap f z :=
by rw [List.filterMap_append, List.filterMap_append]

lemma reverse_append_append :
  List.reverse (x ++ y ++ z) = z.reverse ++ y.reverse ++ x.reverse :=
by rw [List.reverse_append, List.reverse_append, List.append_assoc]

lemma mem_append_append {a : α} :
  a ∈ x ++ y ++ z  ↔  a ∈ x ∨ a ∈ y ∨ a ∈ z  :=
by rw [List.mem_append, List.mem_append, or_assoc]

lemma forall_mem_append_append {p : α → Prop} :
  (∀ a ∈ x ++ y ++ z, p a)  ↔  (∀ a ∈ x, p a) ∧ (∀ a ∈ y, p a) ∧ (∀ a ∈ z, p a)  :=
by rw [List.forall_mem_append, List.forall_mem_append, and_assoc]

lemma flatten_append_append {X Y Z : List (List α)} :
  List.flatten (X ++ Y ++ Z) = X.flatten ++ Y.flatten ++ Z.flatten :=
by rw [List.flatten_append, List.flatten_append]

end list_append_append

section list_replicate


lemma replicate_succ_eq_singleton_append (s : α) (n : ℕ) :
  List.replicate n.succ s = [s] ++ List.replicate n s := by
rfl

lemma replicate_succ_eq_append_singleton (s : α) (n : ℕ) :
  List.replicate n.succ s = List.replicate n s ++ [s] := by
  change List.replicate (n + 1) s = List.replicate n s ++ [s]
  rw [List.replicate_add]
  simp

end list_replicate

section list_flatten

lemma append_flatten_append (L : List (List α)) :
  x ++ (List.map (λ l => l ++ x) L).flatten = (List.map (λ l => x ++ l) L).flatten ++ x := by
  induction L
  · simp
  · simpa


private lemma cons_drop_succ {m : Fin x.length} :
  drop m x = x.get m :: drop m.succ x := by
  simp


-- lemma drop_flatten_of_lt {L : List (List α)} {n : Fin L.length} (notall : n < L.flatten.length) :
  -- ∃ m : Fin L.length, ∃ k : Fin L.length,
    -- L.flatten.drop n = ((L.drop m).drop k ++ (L.drop m.succ)).flatten := by
  -- obtain ⟨m, k, left_half⟩ := drop_flatten_of_lt notall
  -- use    m, k


def n_times (l : List α) (n : ℕ) : List α :=
(List.replicate n l).flatten

infix:100 " ^ " => n_times

end list_flatten

variable [DecidableEq α]

section list_index_of

lemma index_of_append_of_in {a : α} (yes_on_left : a ∈ x) :
  List.idxOf a (x ++ y) =  List.idxOf a x  := by
  exact idxOf_append_of_mem yes_on_left

lemma index_of_append_of_notin {a : α} (not_on_left : a ∉ x) :
  List.idxOf a (x ++ y)  =  x.length  +  List.idxOf a y  := by
  exact idxOf_append_of_notMem not_on_left

end list_index_of

section list_count_in

def count_in (l : List α) (a : α) : ℕ :=
List.sum (List.map (λ s => ite (s = a) 1 0) l)

lemma count_in_nil (a : α) :
  count_in [] a = 0 := by
  rfl

lemma count_in_cons (a b : α) :
  count_in (b :: x) a  =  ite (b = a) 1 0  +  count_in x a  := by
  unfold count_in
  simp

lemma count_in_append (a : α) :
  count_in (x ++ y) a  =  count_in x a  +  count_in y a  := by
  unfold count_in
  simp

lemma count_in_replicate_eq (a : α) (n : ℕ) :
  count_in (List.replicate n a) a  =  n  := by
  unfold count_in
  induction n with
  | zero => rfl
  | succ step ih =>
    simp
    -- rw [List.replicate_succ, List.map_cons, List.sum_cons, ih]
    -- rw [if_pos rfl]
    -- apply Nat.one_add


lemma count_in_replicate_neq {a b : α} (hyp : a ≠ b) (n : ℕ) :
  count_in (List.replicate n a) b  =  0  := by
  unfold count_in
  induction n with
  | zero => rfl
  | succ step ih =>
    rw [List.replicate_succ, List.map_cons, List.sum_cons, ih, add_zero]
    rw [ite_eq_right_iff]
    intro impos
    exfalso
    exact hyp impos

lemma count_in_singleton_eq (a : α) :
  count_in [a] a  =  1  := by
  exact List.count_in_replicate_eq a 1

lemma count_in_singleton_neq {a b : α} (hyp : a ≠ b) :
  count_in [a] b  =  0  := by
  exact List.count_in_replicate_neq hyp 1

lemma count_in_pos_of_in {a : α} (hyp : a ∈ x) :
  count_in x a > 0 := by
  induction x with
  | nil =>
    exfalso
    rw [List.mem_nil_iff] at hyp
    exact hyp
  | cons d l ih =>
    by_contra contr
    rw [not_lt] at contr
    rw [Nat.le_zero_eq] at contr
    rw [List.mem_cons] at hyp
    unfold count_in at contr
    unfold List.map at contr
    simp at contr
    cases hyp with
    | inl hh => exact contr.left hh.symm
    | inr hh =>
      specialize ih hh
      have zero_in_tail : count_in l a = 0 := by
        unfold count_in
        exact contr.right
      rw [zero_in_tail] at ih
      exact Nat.lt_irrefl 0 ih


lemma count_in_zero_of_notin {a : α} (hyp : a ∉ x) :
  count_in x a = 0 := by
  induction x with
  | nil => rfl
  | cons d i ih =>
    unfold count_in
    rw [List.map_cons, List.sum_cons]
    split_ifs with heq
    · exfalso
      have hmem : a ∈ d :: i := by
        subst heq      -- replace d with a everywhere
        simp           -- now goal is `a ∈ a :: i`, which is trivially true
      exact hyp hmem
    · have notin : a ∉ i := by
        exact not_mem_of_not_mem_cons hyp
      specialize ih notin
      ring_nf
      exact Eq.symm ((fun {a b} => Nat.succ_inj.mp) (congrArg Nat.succ (id (Eq.symm ih))))

lemma count_in_flatten (L : List (List α)) (a : α) :
  count_in L.flatten a = List.sum (List.map (λ w => count_in w a) L) := by
  induction L with
  | nil => rfl
  | cons _ _ L_ih =>
    simp [List.flatten, count_in_append, L_ih]

end list_count_in

end List

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

lemma nthLe_mem {l : List α} {n : ℕ} (h : n < l.length) :
  l.nthLe n h ∈ l := by
  induction l generalizing n with
  | nil =>
      cases (Nat.not_lt_zero _ h)
  | cons a l ih =>
      cases n with
      | zero =>
          simp [List.nthLe]
      | succ n =>
          have h' : n < l.length := Nat.lt_of_succ_lt_succ h
          have ih' := ih h'
          simpa [List.nthLe, h'] using (List.mem_cons_of_mem a ih')

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

theorem nthLe_of_eq {l₁ l₂ : List α} (h : l₁ = l₂) {n : Nat} (hn : n < l₁.length) :
    l₁.nthLe n hn = l₂.nthLe n (by simpa [h] using hn) := by
  subst h
  rfl

theorem nthLe_append {l₁ l₂ : List α} {n : Nat}
    (h₁ : n < l₁.length) (h₂ : n < (l₁ ++ l₂).length) :
    (l₁ ++ l₂).nthLe n h₂ = l₁.nthLe n h₁ := by
  induction l₁ generalizing n with
  | nil =>
      cases (Nat.not_lt_zero _ h₁)
  | cons head tail ih =>
      cases n with
      | zero =>
          simp [List.nthLe]
      | succ n =>
          have h₁' : n < tail.length := Nat.lt_of_succ_lt_succ h₁
          have h₂' : n < (tail ++ l₂).length := by
            simpa [List.length_append] using (Nat.lt_of_succ_lt_succ h₂)
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

theorem nthLe_of_mem {l : List α} {a : α} (h : a ∈ l) :
    ∃ n, ∃ h' : n < l.length, l.nthLe n h' = a := by
  exact (mem_iff_nth_le).1 h

theorem nthLe_replicate (a : α) {n i : Nat} (h : i < (List.replicate n a).length) :
    (List.replicate n a).nthLe i h = a := by
  induction n generalizing i with
  | zero =>
      cases (Nat.not_lt_zero _ h)
  | succ n ih =>
      cases i with
      | zero =>
          simp [List.replicate, List.nthLe]
      | succ i =>
          have h' : i < (List.replicate n a).length := by
            simpa [List.length_replicate] using (Nat.lt_of_succ_lt_succ h)
          simpa [List.nthLe] using (ih (i := i) h')

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
