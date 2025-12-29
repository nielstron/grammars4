-- Written by Patrick Johnson and released into the public domain at:
-- https://github.com/user7230724/lean-projects/blob/master/src/list_take_join/main.lean

import Mathlib.Tactic

open Lean Elab Tactic

namespace List

variable {α : Type*}

private noncomputable def get_max [Inhabited α] [LinearOrder α] (P : α → Prop) :=
Classical.epsilon (fun (x : α) => P x ∧ ∀ (y : α), x < y → ¬P y)

private lemma epsilon_eq [Inhabited α] {P : α → Prop} {x : α}
  (h₁ : P x) (h₂ : ∀ (y : α), P y → y = x) : Classical.epsilon P = x :=
by
  have h₃ : P = (fun (y : α) => y = x) := by
    ext y
    constructor
    · intro hy
      exact h₂ y hy
    · intro hy
      simpa [hy]
  subst h₃
  apply Classical.epsilon_singleton

private lemma nat_get_max_spec {P : ℕ → Prop}
  (h₁ : ∃ (x : ℕ), P x) (h₂ : ∃ (x : ℕ), ∀ (y : ℕ), x ≤ y → ¬P y) :
  P (get_max P) ∧ ∀ (x : ℕ), get_max P < x → ¬P x :=
by
  rcases h₁ with ⟨m, h₁⟩
  rcases h₂ with ⟨n, h₂⟩
  induction n with
  | zero =>
    cases h₂ m (zero_le m) h₁
  | succ n ih =>
    simp_rw [Nat.succ_le_iff] at h₂
    by_cases h₃ : P n
    ·
      have : get_max P = n := by
        rw [get_max]
        apply epsilon_eq
        ·
          refine ⟨h₃, ?_⟩
          rintro k hk
          exact h₂ k hk
        ·
          rintro k ⟨h₄, h₅⟩
          by_contra h₆
          have h₆' : k < n ∨ k > n := lt_or_gt_of_ne h₆
          cases h₆' with
          | inl hlt => exact h₅ n hlt h₃
          | inr hgt => exact h₂ k hgt h₄
      rw [this] at *
      exact ⟨h₃, h₂⟩
    ·
      apply ih
      rintro k hk
      rw [le_iff_eq_or_lt] at hk
      rcases hk with rfl | hk
      · exact h₃
      · exact h₂ k hk

private lemma take_eq_take {l : List α} {m n : ℕ} :
  l.take m = l.take n ↔ min m l.length = min n l.length :=
by
  induction l generalizing m n with
  | nil =>
    simp
  | cons x l ih =>
    cases m <;> cases n <;> simp [ih, Nat.succ_min_succ]

private lemma take_add_aux {l : List α} {m n : ℕ} :
  l.take (m + n) = l.take m ++ (l.drop m).take n :=
by
  simpa using (List.take_add (l := l) (i := m) (j := n))

private lemma take_one_drop_eq_of_lt_length' {l : List α} {n : ℕ}
  (h : n < l.length) : (l.drop n).take 1 = [l.get ⟨n, h⟩] :=
by
  simpa using (List.take_one_drop_eq_of_lt_length (l := l) h)

lemma take_join_of_lt {L : List (List α)} {n : ℕ} (notall : n < (List.flatten L).length) :
  ∃ m k : ℕ, ∃ mlt : m < L.length, k < (L.get ⟨m, mlt⟩).length ∧
    (List.flatten L).take n = (List.flatten (L.take m)) ++ (L.get ⟨m, mlt⟩).take k :=
by
  set X := L.length with hX
  set N := (List.flatten L).length with hN
  have notall' : n < N := by
    simpa [hN] using notall
  have hl : L ≠ [] := by
    rintro rfl
    rw [hN] at notall'
    cases notall'
  generalize hP : (fun (m : ℕ) => (List.flatten (L.take m)).length ≤ n) = P
  generalize hm : get_max P = m
  generalize hk : n - (List.flatten (L.take m)).length = k
  have hP0 : P 0 := by
    rw [←hP]
    simp
  have hPX : ∀ (r : ℕ), X ≤ r → ¬P r := by
    rintro r hr
    rw [←hP]
    push_neg
    convert notall'
    ·
      have ht : L.take r = L := (List.take_eq_self_iff L).2 hr
      simpa [ht]
  obtain ⟨hm₁, hm₂⟩ := nat_get_max_spec ⟨0, hP0⟩ ⟨X, hPX⟩
  rw [hm] at hm₁ hm₂
  have hm₃ : ¬P m.succ := hm₂ _ (Nat.lt_succ_self m)
  have mlt : m < L.length := by
    by_contra hx
    have hx' : L.length ≤ m := le_of_not_gt hx
    have hx'' : X ≤ m := by simpa [hX] using hx'
    exact hPX m hx'' hm₁
  refine ⟨m, k, mlt, ?_, ?_⟩
  ·
    rw [←hP] at hm₁ hm₃
    push_neg at hm₃
    by_contra hk₁
    have hk₁' : (L.get ⟨m, mlt⟩).length ≤ k := le_of_not_gt hk₁
    obtain ⟨k', hk'⟩ := Nat.exists_eq_add_of_le hk₁'
    have hk'' :
        n = (L.get ⟨m, mlt⟩).length + k' + (List.flatten (L.take m)).length := by
      replace hk := congr_arg (fun (x : ℕ) => x + (List.flatten (L.take m)).length) hk
      dsimp at hk
      rw [Nat.sub_add_cancel hm₁, hk'] at hk
      simpa [add_assoc, add_left_comm, add_comm] using hk
    have htake : L.take m.succ = L.take m ++ [L.get ⟨m, mlt⟩] := by
      have h1 : L.take (m + 1) = L.take m ++ (L.drop m).take 1 := by
        simpa using (take_add_aux (l := L) (m := m) (n := 1))
      have h2 : (L.drop m).take 1 = [L.get ⟨m, mlt⟩] := by
        simpa using (take_one_drop_eq_of_lt_length' (l := L) (n := m) mlt)
      simpa [Nat.succ_eq_add_one, h2] using h1
    have hlen : (List.flatten (L.take m.succ)).length =
        (List.flatten (L.take m)).length + (L.get ⟨m, mlt⟩).length := by
      rw [htake]
      rw [List.flatten_append, List.length_append]
      have hflat : List.flatten [L.get ⟨m, mlt⟩] = L.get ⟨m, mlt⟩ := by
        simp
      rw [hflat]
    have hm₃' :
        (L.get ⟨m, mlt⟩).length + k' + (List.flatten (L.take m)).length <
          (List.flatten (L.take m)).length + (L.get ⟨m, mlt⟩).length := by
      simpa [hk'', hlen, add_comm, add_left_comm, add_assoc] using hm₃
    have hm₃'' :
        (List.flatten (L.take m)).length + ((L.get ⟨m, mlt⟩).length + k') <
          (List.flatten (L.take m)).length + (L.get ⟨m, mlt⟩).length := by
      simpa [add_comm, add_left_comm, add_assoc] using hm₃'
    have hm₃''' : (L.get ⟨m, mlt⟩).length + k' < (L.get ⟨m, mlt⟩).length := by
      exact lt_of_add_lt_add_left hm₃''
    have hm₃'''' : k' < 0 := by
      have hm₃'''' :
          (L.get ⟨m, mlt⟩).length + k' < (L.get ⟨m, mlt⟩).length + 0 := by
        simpa using hm₃'''
      exact lt_of_add_lt_add_left hm₃''''
    exact (Nat.not_lt_zero _ hm₃'''')
  ·
    have hflatten :
        List.flatten L = List.flatten (L.take m.succ) ++ List.flatten (L.drop m.succ) := by
      have h :=
        congrArg List.flatten (List.take_append_drop (i := m.succ) (l := L))
      have h' :
          List.flatten (L.take m.succ) ++ List.flatten (L.drop m.succ) = List.flatten L := by
        have h' := h
        rw [List.flatten_append] at h'
        exact h'
      exact h'.symm
    rw [hflatten]
    have hn₁ : (List.flatten (L.take m)).length ≤ n := by
      rwa [←hP] at hm₁
    have hn₂ : n < (List.flatten (L.take m.succ)).length := by
      rw [←hP] at hm₃
      push_neg at hm₃
      exact hm₃
    rw [List.take_append_of_le_length (le_of_lt hn₂)]
    have htake : L.take m.succ = L.take m ++ [L.get ⟨m, mlt⟩] := by
      have h1 : L.take (m + 1) = L.take m ++ (L.drop m).take 1 := by
        simpa using (take_add_aux (l := L) (m := m) (n := 1))
      have h2 : (L.drop m).take 1 = [L.get ⟨m, mlt⟩] := by
        simpa using (take_one_drop_eq_of_lt_length' (l := L) (n := m) mlt)
      simpa [Nat.succ_eq_add_one, h2] using h1
    have hflatten_msucc :
        List.flatten (L.take m.succ) =
          List.flatten (L.take m) ++ (L.get ⟨m, mlt⟩) := by
      rw [htake]
      rw [List.flatten_append]
      have hflat : List.flatten [L.get ⟨m, mlt⟩] = L.get ⟨m, mlt⟩ := by
        simp
      rw [hflat]
    rw [hflatten_msucc]
    have : n = (List.flatten (List.take m L)).length + k := by
      have hk' := congr_arg (fun (x : ℕ) => x + (List.flatten (L.take m)).length) hk
      dsimp at hk'
      have hk'' : n = k + (List.flatten (L.take m)).length := by
        simpa [Nat.sub_add_cancel hn₁, add_comm, add_left_comm, add_assoc, -List.length_flatten]
          using hk'
      simpa [add_comm, add_left_comm, add_assoc, -List.length_flatten] using hk''
    subst this
    simpa using (List.take_length_add_append
      (l₁ := List.flatten (L.take m)) (l₂ := L.get ⟨m, mlt⟩) (i := k))

end List
