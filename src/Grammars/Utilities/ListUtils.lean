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
    refine And.intro ?_ ?_;
    · in_list_explicit)

namespace List

variables {α β : Type*} {x y z : List α}

section list_append_append

lemma length_append_append :
  List.length (x ++ y ++ z) = x.length + y.length + z.length :=
by rw [List.length_append, List.length_append]

lemma map_append_append {f : α → β} :
  List.map f (x ++ y ++ z) = List.map f x ++ List.map f y ++ List.map f z :=
by rw [List.map_append, List.map_append]

lemma filter_map_append_append {f : α → Option β} :
  List.filter_map f (x ++ y ++ z) = List.filter_map f x ++ List.filter_map f y ++ List.filter_map f z :=
by rw [List.filter_map_append, List.filter_map_append]

lemma reverse_append_append :
  List.reverse (x ++ y ++ z) = z.reverse ++ y.reverse ++ x.reverse :=
by rw [List.reverse_append, List.reverse_append, List.append_assoc]

lemma mem_append_append {a : α} :
  a ∈ x ++ y ++ z  ↔  a ∈ x ∨ a ∈ y ∨ a ∈ z  :=
by rw [List.mem_append, List.mem_append, or_assoc]

lemma forall_mem_append_append {p : α → Prop} :
  (∀ a ∈ x ++ y ++ z, p a)  ↔  (∀ a ∈ x, p a) ∧ (∀ a ∈ y, p a) ∧ (∀ a ∈ z, p a)  :=
by rw [List.forall_mem_append, List.forall_mem_append, and_assoc]

lemma join_append_append {X Y Z : List (List α)} :
  List.join (X ++ Y ++ Z) = X.join ++ Y.join ++ Z.join :=
by rw [List.join_append, List.join_append]

end list_append_append

section list_repeat

lemma repeat_zero (s : α) :
  List.repeat s 0 = [] :=
rfl

lemma repeat_succ_eq_singleton_append (s : α) (n : ℕ) :
  List.repeat s n.succ = [s] ++ List.repeat s n :=
rfl

lemma repeat_succ_eq_append_singleton (s : α) (n : ℕ) :
  List.repeat s n.succ = List.repeat s n ++ [s] :=
begin
  change List.repeat s (n + 1) = List.repeat s n ++ [s],
  rw List.repeat_add,
  refl,
end

end list_repeat

section list_join

lemma join_singleton : [x].join = x :=
by rw [List.join, List.join, List.append_nil]

lemma append_join_append (L : List (List α)) :
  x ++ (List.map (λ l, l ++ x) L).join = (List.map (λ l, x ++ l) L).join ++ x :=
begin
  induction L,
  {
    rw [List.map_nil, List.join, List.append_nil, List.map_nil, List.join, List.nil_append],
  },
  {
    rw [
      List.map_cons, List.join, List.map_cons, List.join, List.append_assoc, L_ih,
      List.append_assoc, List.append_assoc
    ],
  },
end

lemma reverse_join (L : List (List α)) :
  L.join.reverse = (List.map List.reverse L).reverse.join :=
begin
  induction L,
  {
    refl,
  },
  {
    rw [
      List.join, List.reverse_append, L_ih,
      List.map_cons, List.reverse_cons, List.join_append, List.join_singleton
    ],
  },
end

private lemma cons_drop_succ {m : ℕ} (mlt : m < x.length) :
  drop m x = x.nthLe m mlt :: drop m.succ x :=
begin
  induction x with d l ih generalizing m,
  {
    exfalso,
    rw length at mlt,
    exact Nat.not_lt_zero m mlt,
  },
  cases m,
  {
    simp,
  },
  rw [drop, drop, nth_le],
  apply ih,
end

lemma drop_join_of_lt {L : List (List α)} {n : ℕ} (notall : n < L.join.length) :
  ∃ m k : ℕ, ∃ mlt : m < L.length, k < (L.nthLe m mlt).length ∧
    L.join.drop n = (L.nthLe m mlt).drop k ++ (L.drop m.succ).join :=
begin
  obtain ⟨m, k, mlt, klt, left_half⟩ := take_join_of_lt notall,
  use    [m, k, mlt, klt],
  have L_two_parts := congr_arg List.join (List.take_append_drop m L),
  rw List.join_append at L_two_parts,
  have whole := List.take_append_drop n L.join,
  rw left_half at whole,
  have important := eq.trans whole L_two_parts.symm,
  rw append_assoc at important,
  have right_side := append_left_cancel important,
  have auxi : (drop m L).join = (L.nthLe m mlt :: drop m.succ L).join,
  {
    apply congr_arg,
    apply cons_drop_succ,
  },
  rw join at auxi,
  rw auxi at right_side,
  have near_result :
    take k (L.nthLe m mlt) ++ drop n L.join =
    take k (L.nthLe m mlt) ++ drop k (L.nthLe m mlt) ++ (drop m.succ L).join,
  {
    convert right_side,
    rw List.take_append_drop,
  },
  rw append_assoc at near_result,
  exact append_left_cancel near_result,
end

def n_times (l : List α) (n : ℕ) : List α :=
(List.repeat l n).join

infix ` ^ ` : 100 := n_times

end list_join

variables [decidable_eq α]

section list_index_of

lemma index_of_append_of_in {a : α} (yes_on_left : a ∈ x) :
  index_of a (x ++ y)  =  index_of a x  :=
begin
  induction x with d l ih,
  {
    exfalso,
    exact not_mem_nil a yes_on_left,
  },
  rw List.cons_append,
  by_cases ad : a = d,
  {
    rw index_of_cons_eq _ ad,
    rw index_of_cons_eq _ ad,
  },
  rw index_of_cons_ne _ ad,
  rw index_of_cons_ne _ ad,
  apply congr_arg,
  apply ih,
  exact mem_of_ne_of_mem ad yes_on_left,
end

lemma index_of_append_of_notin {a : α} (not_on_left : a ∉ x) :
  index_of a (x ++ y)  =  x.length  +  index_of a y  :=
begin
  induction x with d l ih,
  {
    rw [List.nil_append, List.length, zero_add],
  },
  rw [
    List.cons_append,
    index_of_cons_ne _ (ne_of_not_mem_cons not_on_left),
    List.length,
    ih (not_mem_of_not_mem_cons not_on_left),
    Nat.succ_add
  ],
end

end list_index_of

section list_count_in

def count_in (l : List α) (a : α) : ℕ :=
List.sum (List.map (λ s, ite (s = a) 1 0) l)

lemma count_in_nil (a : α) :
  count_in [] a = 0 :=
begin
  refl,
end

lemma count_in_cons (a b : α) :
  count_in (b :: x) a  =  ite (b = a) 1 0  +  count_in x a  :=
begin
  unfold count_in,
  rw List.map_cons,
  rw List.sum_cons,
end

lemma count_in_append (a : α) :
  count_in (x ++ y) a  =  count_in x a  +  count_in y a  :=
begin
  unfold count_in,
  rw List.map_append,
  rw List.sum_append,
end

lemma count_in_repeat_eq (a : α) (n : ℕ) :
  count_in (List.repeat a n) a  =  n  :=
begin
  unfold count_in,
  induction n with m ih,
  {
    refl,
  },
  rw [List.repeat_succ, List.map_cons, List.sum_cons, ih],
  rw if_pos rfl,
  apply Nat.one_add,
end

lemma count_in_repeat_neq {a b : α} (hyp : a ≠ b) (n : ℕ) :
  count_in (List.repeat a n) b  =  0  :=
begin
  unfold count_in,
  induction n with m ih,
  {
    refl,
  },
  rw [List.repeat_succ, List.map_cons, List.sum_cons, ih, add_zero],
  rw ite_eq_right_iff,
  intro impos,
  exfalso,
  exact hyp impos,
end

lemma count_in_singleton_eq (a : α) :
  count_in [a] a  =  1  :=
begin
  exact List.count_in_repeat_eq a 1,
end

lemma count_in_singleton_neq {a b : α} (hyp : a ≠ b) :
  count_in [a] b  =  0  :=
begin
  exact List.count_in_repeat_neq hyp 1,
end

lemma count_in_pos_of_in {a : α} (hyp : a ∈ x) :
  count_in x a > 0 :=
begin
  induction x with d l ih,
  {
    exfalso,
    rw List.mem_nil_iff at hyp,
    exact hyp,
  },
  by_contradiction contr,
  rw not_lt at contr,
  rw Nat.le_zero_iff at contr,
  rw List.mem_cons_eq at hyp,
  unfold count_in at contr,
  unfold List.map at contr,
  simp at contr,
  cases hyp,
  {
    exact contr.left hyp.symm,
  },
  specialize ih hyp,
  have zero_in_tail : count_in l a = 0,
  {
    unfold count_in,
    exact contr.right,
  },
  rw zero_in_tail at ih,
  exact Nat.lt_irrefl 0 ih,
end

lemma count_in_zero_of_notin {a : α} (hyp : a ∉ x) :
  count_in x a = 0 :=
begin
  induction x with d l ih,
  {
    refl,
  },
  unfold count_in,
  rw [List.map_cons, List.sum_cons, add_eq_zero_iff, ite_eq_right_iff],
  split,
  {
    simp only [Nat.one_ne_zero],
    exact (List.ne_of_not_mem_cons hyp).symm,
  },
  {
    exact ih (List.not_mem_of_not_mem_cons hyp),
  },
end

lemma count_in_join (L : List (List α)) (a : α) :
  count_in L.join a = List.sum (List.map (λ w, count_in w a) L) :=
begin
  induction L,
  {
    refl,
  },
  {
    rw [List.join, List.count_in_append, List.map, List.sum_cons, L_ih],
  },
end

end list_count_in

end List
