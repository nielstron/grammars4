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
