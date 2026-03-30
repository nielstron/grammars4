/-
Copyright (c) 2026 Harmonic, Niels Mündler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Grammars.Classes.DetContextFree.Basics.DCFL
import Grammars.Classes.DetContextFree.ClosureProperties.Complement
import Grammars.Classes.ContextFree.Basics.Ogden

/-! # DCFLs are a strict subset of CFLs

This file shows that DCFLs are a subset of the CFLs
and that they are a strict subset

--/

-- ============================================================================
-- DCFL inclusion into CFL
-- ============================================================================

theorem is_CF_of_is_DCFL {T : Type} [Fintype T] {L : Language T} (h : is_DCFL L) : is_CF L := by
  obtain ⟨Q, S, _, _, M, rfl⟩ := h
  exact is_CF_of_is_PDA M.is_PDA_acceptsByFinalState


-- ============================================================================
-- The main result: CFL ⊋ DCFL (strict inclusion)
-- ============================================================================

/-- If every CFL (over a fixed finite alphabet `T`) were a DCFL, then every CFL's
    complement would also be a CFL. -/
theorem complement_CF_of_all_CF_DCFL {T : Type} [Fintype T]
    (h : ∀ L : Language T, is_CF L → is_DCFL L) :
    ∀ L : Language T, is_CF L → is_CF Lᶜ :=
  fun L hCF => is_CF_of_is_DCFL (is_DCFL_compl (h L hCF))

/-- `lang_eq_any ⊓ lang_any_eq = lang_eq_eq` -/
private lemma lang_intersection_eq :
    lang_eq_any ⊓ lang_any_eq = lang_eq_eq := by
  ext w
  exact ⟨lang_eq_eq_of_intersection, intersection_of_lang_eq_eq⟩

/-- CFL over Fin 3 is NOT closed under complement. This is a specialized version
    of `nnyCF_of_complement_CF` that works over a fixed alphabet. -/
private lemma not_complement_closed_Fin3 :
    ¬ (∀ L : Language (Fin 3), is_CF L → is_CF Lᶜ) := by
  intro h
  -- If CFL were closed under complement, then Lᶜ₁ and Lᶜ₂ are CFL
  have h1 : is_CF lang_eq_anyᶜ := h _ CF_lang_eq_any
  have h2 : is_CF lang_any_eqᶜ := h _ CF_lang_any_eq
  -- Their union is CFL
  have h_union : is_CF (lang_eq_anyᶜ + lang_any_eqᶜ) :=
    CF_of_CF_u_CF _ _ ⟨h1, h2⟩
  -- The complement of their union is CFL (by the hypothesis)
  have h_inter : is_CF (lang_eq_anyᶜ + lang_any_eqᶜ)ᶜ :=
    h _ h_union
  -- (L₁ᶜ ∪ L₂ᶜ)ᶜ = L₁ ∩ L₂
  have h_eq : (lang_eq_anyᶜ + lang_any_eqᶜ)ᶜ = lang_eq_any ⊓ lang_any_eq := by
    simp only [Language.add_def]; rw [Set.compl_union]; simp [compl_compl]; rfl
  rw [h_eq, lang_intersection_eq] at h_inter
  exact notCF_lang_eq_eq h_inter

/-- There exist context-free languages over `Fin 3` that are not deterministic
    context-free. This is the strict inclusion DCFL ⊊ CFL. -/
theorem exists_CF_not_DCFL : ∃ L : Language (Fin 3), is_CF L ∧ ¬ is_DCFL L := by
  by_contra h_all
  push_neg at h_all
  -- h_all : ∀ L : Language (Fin 3), is_CF L → is_DCFL L
  exact not_complement_closed_Fin3 (complement_CF_of_all_CF_DCFL h_all)

-- ============================================================================
-- The explicit witness: {aⁱ bʲ cᵏ | i = j ∨ j = k}
-- ============================================================================

section explicit_witness

/-- The language `{aⁿ bⁿ cᵐ | n, m ∈ ℕ}` over `{0, 1, 2}` = `{a, b, c}`. -/
def lang_anbnck : Language (Fin 3) :=
  fun w => ∃ n m : ℕ, w = List.replicate n 0 ++ List.replicate n 1 ++ List.replicate m 2

/-- The language `{aⁿ bᵐ cᵐ | n, m ∈ ℕ}` over `{0, 1, 2}` = `{a, b, c}`. -/
def lang_anbmcm : Language (Fin 3) :=
  fun w => ∃ n m : ℕ, w = List.replicate n 0 ++ List.replicate m 1 ++ List.replicate m 2

/-- The language `{aⁱ bʲ cᵏ | i = j ∨ j = k}` over `{0, 1, 2}`.
    The standard explicit witness of a CFL that is not a DCFL. -/
def lang_aibjck : Language (Fin 3) :=
  fun w => ∃ i j k : ℕ,
    w = List.replicate i 0 ++ List.replicate j 1 ++ List.replicate k 2 ∧ (i = j ∨ j = k)

/-- `lang_aibjck` equals the union of `lang_anbnck` and `lang_anbmcm`. -/
theorem lang_aibjck_eq_union : lang_aibjck = lang_anbnck + lang_anbmcm := by
  ext w
  simp only [Language.mem_add]
  constructor
  · rintro ⟨i, j, k, hw, hij | hjk⟩
    · left; exact ⟨i, k, hij ▸ hw⟩
    · right; exact ⟨i, j, hjk ▸ hw⟩
  · rintro (⟨n, m, hw⟩ | ⟨n, m, hw⟩)
    · exact ⟨n, n, m, hw, Or.inl rfl⟩
    · exact ⟨n, m, m, hw, Or.inr rfl⟩

/-- `{aⁿ bⁿ cᵐ}` is context-free. -/
theorem is_CF_lang_anbnck : is_CF lang_anbnck := by
  have h : lang_anbnck = lang_eq_any := by
    ext w; unfold lang_anbnck lang_eq_any a_ b_ c_; rfl
  rw [h]; exact CF_lang_eq_any

/-- `{aⁿ bᵐ cᵐ}` is context-free. -/
theorem is_CF_lang_anbmcm : is_CF lang_anbmcm := by
  have h : lang_anbmcm = lang_any_eq := by
    ext w; unfold lang_anbmcm lang_any_eq a_ b_ c_; rfl
  rw [h]; exact CF_lang_any_eq

/-- `{aⁱ bʲ cᵏ | i = j ∨ j = k}` is context-free. -/
theorem lang_aibjck_CFL : is_CF lang_aibjck := by
  rw [lang_aibjck_eq_union]
  exact CF_of_CF_u_CF _ _ ⟨is_CF_lang_anbnck, is_CF_lang_anbmcm⟩



/-- The language `{a^i b^j c^k | i ≠ j ∧ j ≠ k}` over `Fin 3`. -/
def lang_neq_neq : Language (Fin 3) :=
  fun w => ∃ i j k : ℕ,
    w = List.replicate i 0 ++ List.replicate j 1 ++ List.replicate k 2 ∧ i ≠ j ∧ j ≠ k

/-- The regular language `a*b*c*` over `Fin 3`. -/
def lang_abc_star : Language (Fin 3) :=
  fun w => ∃ i j k : ℕ, w = List.replicate i 0 ++ List.replicate j 1 ++ List.replicate k 2

/-- Decomposition of a word in `a*b*c*` into components is unique. -/
lemma abc_decomp_unique {i j k i' j' k' : ℕ}
    (h : List.replicate i (0 : Fin 3) ++ List.replicate j 1 ++ List.replicate k 2 =
         List.replicate i' 0 ++ List.replicate j' 1 ++ List.replicate k' 2) :
    i = i' ∧ j = j' ∧ k = k' := by
  have := congr_arg ( fun b => List.count 0 b ) h ; have := congr_arg ( fun b => List.count 1 b ) h ; have := congr_arg ( fun b => List.count 2 b ) h ; norm_num [ List.count_replicate ] at * ; aesop;

/-- The complement of `lang_aibjck` intersected with `a*b*c*` equals `lang_neq_neq`. -/
lemma compl_aibjck_inter_abc_eq_neq_neq :
    lang_aibjckᶜ ⊓ lang_abc_star = lang_neq_neq := by
  ext w
  simp
  constructor;
  · rintro ⟨ hw₁, ⟨ i, j, k, rfl ⟩ ⟩ ; exact ⟨ i, j, k, rfl, by intros hi; exact hw₁ ⟨ i, j, k, rfl, Or.inl hi ⟩, by intros hj; exact hw₁ ⟨ i, j, k, rfl, Or.inr hj ⟩ ⟩ ;
  · rintro ⟨ i, j, k, rfl, hij, hjk ⟩ ; exact ⟨ fun ⟨ i', j', k', h₁, h₂ ⟩ => by have := abc_decomp_unique h₁; aesop, i, j, k, rfl ⟩ ;

/-
PROVIDED SOLUTION
The maxHeartbeats is already set to 1600000 for this lemma. Construct a DFA (Fin 3) (Fin 4) for the language a*b*c*. Use `decide` or `fin_cases` for the finite case analyses. The DFA:
- step function: use a function that's written with pattern matching on Fin 4 and Fin 3 values
- start = 0
- accept = {0, 1, 2}

Then show it accepts exactly lang_abc_star. Use induction on the word, with reverseRecOn.

For the forward direction (DFA accepts → lang_abc_star): track what the DFA state tells us about the word. State 0 = only 0s seen. State 1 = 0s then 1s seen. State 2 = 0s then 1s then 2s seen. State 3 = invalid.

For the backward direction (lang_abc_star → DFA accepts): given w = rep i 0 ++ rep j 1 ++ rep k 2, compute the DFA run. State goes 0→...→0→1→...→1→2→...→2 which is accepting.

Key insight: define the DFA step as `![![0,1,2,3], ![3,1,2,3], ![3,3,2,3], ![3,3,3,3]] q a` using matrix notation for Fin 4 × Fin 3 → Fin 4. Or define using explicit if-then-else.

For the backward direction proof, use induction on i, then j, then k, computing the DFA evaluation step by step using List.foldl_append and List.foldl_replicate or similar.
-/
set_option maxHeartbeats 1600000 in
/-- `lang_abc_star` (a*b*c*) is a regular language. -/
lemma isRegular_lang_abc_star : lang_abc_star.IsRegular := by
  -- Define the DFA that accepts a*b*c*.
  let dfa : DFA (Fin 3) (Fin 4) := {
    step := fun q a => if q = 0 ∧ a = 0 then 0 else if q = 0 ∧ a = 1 then 1 else if q = 0 ∧ a = 2 then 2 else if q = 1 ∧ a = 0 then 3 else if q = 1 ∧ a = 1 then 1 else if q = 1 ∧ a = 2 then 2 else if q = 2 ∧ a = 0 then 3 else if q = 2 ∧ a = 1 then 3 else if q = 2 ∧ a = 2 then 2 else 3,
    start := 0,
    accept := {0, 1, 2}
  };
  refine' ⟨ Fin 4, inferInstance, dfa, _ ⟩;
  ext w
  simp [DFA.accepts];
  constructor;
  · intro hw
    have h_state : ∀ w : List (Fin 3), dfa.evalFrom dfa.start w = 0 → ∃ i : ℕ, w = List.replicate i 0 := by
      intro w hw
      induction' w using List.reverseRecOn with w ih;
      · exists 0;
      · fin_cases ih <;> simp +decide [ dfa ] at hw ⊢;
        · rename_i h; rcases h hw with ⟨ i, rfl ⟩ ; exact ⟨ i + 1, by simp +decide [ List.replicate_succ' ] ⟩ ;
        · grind;
        · grind +ring
    have h_state1 : ∀ w : List (Fin 3), dfa.evalFrom dfa.start w = 1 → ∃ i j : ℕ, w = List.replicate i 0 ++ List.replicate j 1 := by
      intro w hw; induction' w using List.reverseRecOn with w ih <;> simp_all +decide [ DFA.evalFrom ] ;
      by_cases h : List.foldl dfa.step dfa.start w = 1 <;> simp_all +decide [ DFA.step ];
      · rcases ‹∃ i j : ℕ, w = List.replicate i 0 ++ List.replicate j 1› with ⟨ i, j, rfl ⟩ ; use i, j + 1; simp +decide [ List.replicate_add ] ;
        grind +splitImp;
      · rcases h : List.foldl dfa.step dfa.start w with ( _ | _ | _ | _ ) <;> simp_all +decide [ Fin.forall_fin_succ ];
        · rcases h_state w h with ⟨ i, rfl ⟩ ; use i, 1 ; simp +decide [ hw ] ;
          grind +splitImp;
        · grind;
        · grind +ring
    have h_state2 : ∀ w : List (Fin 3), dfa.evalFrom dfa.start w = 2 → ∃ i j k : ℕ, w = List.replicate i 0 ++ List.replicate j 1 ++ List.replicate k 2 := by
      intro w hw
      induction' w using List.reverseRecOn with w ih;
      · exists 0, 0, 0;
      · simp +zetaDelta at *;
        fin_cases ih <;> simp +decide [ * ] at hw ⊢;
        · split_ifs at hw <;> contradiction;
        · grind +ring;
        · rename_i h;
          by_cases h2 : dfa.evalFrom dfa.start w = 2;
          · obtain ⟨ i, j, k, rfl ⟩ := h h2; exact ⟨ i, j, k + 1, by simp +decide [ List.replicate_add ] ⟩ ;
          · by_cases h3 : dfa.evalFrom dfa.start w = 0 <;> by_cases h4 : dfa.evalFrom dfa.start w = 1 <;> simp +decide [ h3, h4 ] at hw h2 ⊢;
            · cases h3.symm.trans h4;
            · obtain ⟨ i, hi ⟩ := h_state w h3; use i, 0, 1; simp +decide [ hi ] ;
            · obtain ⟨ i, j, rfl ⟩ := h_state1 w h4; exact ⟨ i, j, 1, by simp +decide [ List.replicate ] ⟩ ;
            · grind +ring;
    rcases hw with ( hw | hw | hw ) <;> [ exact Exists.elim ( h_state w hw ) fun i hi => ⟨ i, 0, 0, by simpa using hi ⟩ ; exact Exists.elim ( h_state1 w hw ) fun i hi => Exists.elim hi fun j hj => ⟨ i, j, 0, by simpa using hj ⟩ ; exact Exists.elim ( h_state2 w hw ) fun i hi => Exists.elim hi fun j hj => Exists.elim hj fun k hk => ⟨ i, j, k, by simpa using hk ⟩ ];
  · rintro ⟨ i, j, k, rfl ⟩ ; simp +decide [ DFA.acceptsFrom ] ;
    induction i <;> simp_all +decide [ DFA.evalFrom ];
    · induction j <;> simp_all +decide [ List.replicate ];
      · induction k <;> simp_all +decide [ List.replicate ];
        · exact Or.inl rfl;
        · rename_i n ih;
          induction n <;> simp_all +decide [ List.replicate ];
          · grind;
          · grind;
      · rename_i n ih;
        induction n <;> simp_all +decide [ List.replicate ];
        · induction k <;> simp_all +decide [ List.replicate ];
          · grind +locals;
          · grind +ring;
        · grind +ring;
    · grind

private lemma lang_neq_neq_count {w : List (Fin 3)} (hw : w ∈ lang_neq_neq) :
    List.count 0 w ≠ List.count 1 w ∧ List.count 1 w ≠ List.count 2 w := by
  obtain ⟨ i, j, k, rfl, hij, hjk ⟩ := hw; simp +decide [ List.count_append, List.count_replicate ] ; aesop;

/-
PROBLEM
For our specific word and marking predicate, marked positions correspond exactly
    to positions containing symbol 1. This connects countMarkedIn with List.count.

PROVIDED SOLUTION
From h_vy_marked, at least one of countMarkedIn P u.length v.length or countMarkedIn P (u.length + v.length + x.length) y.length is positive. Suppose countMarkedIn P u.length v.length > 0 (the other case is symmetric). By the definition of countMarkedIn, there exists i < v.length such that P(u.length + i). Substituting hP, this means 2*n ≤ u.length + i < 2*n + n.

Now, from h_split, the (u.length + i)-th element of the word (List.replicate (2*n) 0 ++ List.replicate n 1 ++ List.replicate (2*n) 2) equals v[i] (because h_split says the word = u ++ v ++ x ++ y ++ z, and position u.length + i with i < v.length is in v's range).

Also, the (u.length + i)-th element of (List.replicate (2*n) 0 ++ List.replicate n 1 ++ List.replicate (2*n) 2) at a position k with 2*n ≤ k < 3*n is 1 (it's in the 1s block).

So v[i] = 1, meaning 1 ∈ v, hence List.count 1 v ≥ 1, hence β ≥ 1.

Similarly if countMarkedIn for y is positive, then List.count 1 y ≥ 1.

Key approach: unfold countMarkedIn to show ∃ i in range with P, then use List.getElem on the split to show the element is 1. Use List.count_pos_iff_mem or similar to get count ≥ 1.
-/
private lemma β_pos_of_vy_marked {n : ℕ} {u v x y z : List (Fin 3)}
    (h_split : List.replicate (2 * n) (0 : Fin 3) ++ List.replicate n 1 ++
               List.replicate (2 * n) 2 = u ++ v ++ x ++ y ++ z)
    {P : ℕ → Prop} [DecidablePred P]
    (hP : P = fun k => 2 * n ≤ k ∧ k < 2 * n + n)
    (h_vy_marked : 0 < countMarkedIn P u.length v.length +
                       countMarkedIn P (u.length + v.length + x.length) y.length) :
    1 ≤ List.count 1 v + List.count 1 y := by
      -- By definition of countMarkedIn, if countMarkedIn P (u.length + v.length + x.length) y.length > 0, then there exists an i in y such that P(u.length + v.length + x.length + i).
      by_cases h_count_y : countMarkedIn P (u.length + v.length + x.length) y.length > 0;
      · obtain ⟨i, hi⟩ : ∃ i, i < y.length ∧ P (u.length + v.length + x.length + i) := by
          contrapose! h_count_y; simp_all +decide [ countMarkedIn ] ;
        have hy1 : (u ++ v ++ x ++ y ++ z)[u.length + v.length + x.length + i]! = 1 := by
          grind;
        grind +qlia;
      · -- Since countMarkedIn P u.length v.length > 0, there exists an i in v such that P(u.length + i).
        obtain ⟨i, hi⟩ : ∃ i < v.length, 2 * n ≤ u.length + i ∧ u.length + i < 2 * n + n := by
          unfold countMarkedIn at h_vy_marked; simp_all +decide [ Finset.sum_range_succ', List.count ] ;
          obtain ⟨ i, hi ⟩ := h_vy_marked.resolve_right ( by unfold countMarkedIn at h_count_y; aesop ) ; use i; aesop;
        generalize_proofs at *; (
        -- Since $u.length + i$ is in the range $[2n, 3n)$, the $(u.length + i)$-th element of the word is $1$.
        have h_element_one : (u ++ v ++ x ++ y ++ z)[u.length + i]! = 1 := by
          grind +ring
        generalize_proofs at *; (
        grind +qlia))

/-
PROVIDED SOLUTION
The key insight: for our specific word w and marking predicate P, every 1 in a substring corresponds to a marked position, and vice versa. So countMarkedIn in a range equals the count of 1s.

Step 1: Use countMarkedIn_add twice to split:
  countMarkedIn P u.length (v.length + x.length + y.length)
  = countMarkedIn P u.length v.length + countMarkedIn P (u.length + v.length) (x.length + y.length)
  = countMarkedIn P u.length v.length + countMarkedIn P (u.length + v.length) x.length + countMarkedIn P (u.length + v.length + x.length) y.length

Step 2: Show count 1 v ≤ countMarkedIn P u.length v.length and count 1 y ≤ countMarkedIn P (u.length + v.length + x.length) y.length. This is because every 1 in v is at a marked position: if v[i] = 1, then w[u.length + i] = 1 (from h_split), which means position u.length + i is in the 1s block [2n, 3n), so P(u.length + i) is true.

Step 3: Therefore β = count 1 v + count 1 y ≤ countMarkedIn P u.length v.length + countMarkedIn P (...) y.length ≤ countMarkedIn P u.length (v.length + x.length + y.length) ≤ p.

Alternative simpler approach: Show directly that β ≤ countMarkedIn P u.length (v.length + x.length + y.length). The vxy substring of w has length v.length + x.length + y.length, starting at offset u.length. Each 1 in v or y is at a marked position, so count 1 v + count 1 y ≤ total marked positions in vxy range = countMarkedIn P u.length (v.length + x.length + y.length) ≤ p.
-/
private lemma β_le_p_of_vxy_marked {n p : ℕ} {u v x y z : List (Fin 3)}
    (h_split : List.replicate (2 * n) (0 : Fin 3) ++ List.replicate n 1 ++
               List.replicate (2 * n) 2 = u ++ v ++ x ++ y ++ z)
    {P : ℕ → Prop} [DecidablePred P]
    (hP : P = fun k => 2 * n ≤ k ∧ k < 2 * n + n)
    (h_vxy_marked : countMarkedIn P u.length (v.length + x.length + y.length) ≤ p) :
    List.count 1 v + List.count 1 y ≤ p := by
      refine le_trans ?_ h_vxy_marked;
      -- By definition of $P$, we know that every 1 in $v$ or $y$ is at a marked position.
      have h_countMarkedIn_vy : ∀ (s : List (Fin 3)) (start : ℕ) (len : ℕ), countMarkedIn P start len ≥ List.count 1 (List.map (fun i => (u ++ v ++ x ++ y ++ z)[start + i]!) (List.range len)) := by
        intros s start len
        have h_countMarkedIn_vy : ∀ (i : ℕ), i < len → (u ++ v ++ x ++ y ++ z)[start + i]! = 1 → P (start + i) := by
          intro i hi h; replace h_split := congr_arg ( fun l => l[start + i]! ) h_split; simp_all +decide ;
          grind +ring;
        have h_countMarkedIn_vy : List.count 1 (List.map (fun i => (u ++ v ++ x ++ y ++ z)[start + i]!) (List.range len)) ≤ Finset.card (Finset.filter (fun i => (u ++ v ++ x ++ y ++ z)[start + i]! = 1) (Finset.range len)) := by
          rw [ List.count ];
          rw [ List.countP_map ];
          rw [ List.countP_eq_length_filter ] ; aesop;
        exact h_countMarkedIn_vy.trans ( Finset.card_mono <| fun i hi => by aesop );
      refine le_trans ?_ ( h_countMarkedIn_vy [] u.length ( v.length + x.length + y.length ) );
      rw [ show List.map ( fun i => ( u ++ v ++ x ++ y ++ z)[u.length + i]! ) ( List.range ( v.length + x.length + y.length ) ) = v ++ x ++ y from ?_ ];
      · simp +arith +decide [ List.count_append ];
      · refine' List.ext_get _ _ <;> simp +decide [ add_assoc ];
        grind +ring

/-
PROBLEM
If the pumped word is in lang_neq_neq (hence sorted), v is a contiguous substring
    of a sorted word with two distinct elements, and the pump index is ≥ 2, then
    v^+^i₀ would need to be both sorted (substring of sorted pumped word) and not sorted
    (by nTimes_not_chain'_of_distinct).

PROVIDED SOLUTION
1. The original word w = 0^{2n} ++ 1^n ++ 2^{2n} is sorted (Chain' (· ≤ ·)) by chain'_replicate_abc.
2. From h_split, w = u ++ v ++ x ++ y ++ z. Rewrite with List.append_assoc to get w = (u ++ v) ++ (x ++ y ++ z). By chain'_middle, v is Chain' (· ≤ ·).
3. The pumped word is in lang_neq_neq, so it equals 0^a ++ 1^b ++ 2^c for some a,b,c. By chain'_replicate_abc, it is Chain' (· ≤ ·).
4. The pumped word = u ++ v^+^i₀ ++ x ++ y^+^i₀ ++ z. Rewrite with List.append_assoc to get (u ++ v^+^i₀) ++ (x ++ y^+^i₀ ++ z). By chain'_middle, v^+^i₀ is Chain' (· ≤ ·).
5. But v is sorted with distinct elements (a ≠ b, a ∈ v, b ∈ v) and i₀ ≥ 2. By nTimes_not_chain'_of_distinct, v^+^i₀ is NOT Chain' (· ≤ ·).
6. Contradiction between steps 4 and 5.

Key: use `simp only [List.append_assoc]` or `rw [List.append_assoc, List.append_assoc]` to normalize the list association before applying chain'_middle.
-/
private lemma sorted_pump_v_false {n : ℕ} {u v x y z : List (Fin 3)} {i₀ : ℕ}
    (h_split : List.replicate (2 * n) (0 : Fin 3) ++ List.replicate n 1 ++
               List.replicate (2 * n) 2 = u ++ v ++ x ++ y ++ z)
    (h_pump_i₀ : u ++ v ^+^ i₀ ++ x ++ y ^+^ i₀ ++ z ∈ lang_neq_neq)
    (h_i₀_ge_2 : 2 ≤ i₀)
    {a b : Fin 3} (hab : a ≠ b) (hav : a ∈ v) (hbv : b ∈ v) : False := by
      obtain ⟨ i, j, k, h ⟩ := h_pump_i₀;
      have := List.isChain_append.mp ( show List.IsChain ( · ≤ · ) ( u ++ v ^+^ i₀ ++ x ++ y ^+^ i₀ ++ z ) from by
                                        rw [ h.1 ] ; exact chain'_replicate_abc _ _ _; ) ; simp_all +decide [ List.isChain_append ] ;
      exact absurd ( nTimes_not_chain'_of_distinct ( show List.IsChain ( · ≤ · ) ( v ) from by
                                                      have hv_sorted : List.IsChain (· ≤ ·) (List.replicate (2 * n) (0 : Fin 3) ++ List.replicate n 1 ++ List.replicate (2 * n) 2) := by
                                                        exact chain'_replicate_abc _ _ _;
                                                      grind +splitImp ) ⟨ a, b, hab, hav, hbv ⟩ ( by linarith ) ) ( by aesop )

/-
PROVIDED SOLUTION
Same argument as sorted_pump_v_false but for y instead of v.

1. w = 0^{2n} ++ 1^n ++ 2^{2n} is sorted by chain'_replicate_abc.
2. From h_split, w = u ++ v ++ x ++ y ++ z. The association ((u++v++x) ++ y) ++ z already has y as the second-to-last piece. chain'_middle directly extracts y as Chain' (· ≤ ·).
3. The pumped word ∈ lang_neq_neq means it's 0^a ++ 1^b ++ 2^c, hence sorted by chain'_replicate_abc.
4. The pumped word = (((u ++ v^+^i₀) ++ x) ++ y^+^i₀) ++ z. chain'_middle directly extracts y^+^i₀ as Chain' (· ≤ ·).
5. y is sorted with distinct elements and i₀ ≥ 2, so nTimes_not_chain'_of_distinct gives ¬(y^+^i₀).Chain' (· ≤ ·). Contradiction.
-/
private lemma sorted_pump_y_false {n : ℕ} {u v x y z : List (Fin 3)} {i₀ : ℕ}
    (h_split : List.replicate (2 * n) (0 : Fin 3) ++ List.replicate n 1 ++
               List.replicate (2 * n) 2 = u ++ v ++ x ++ y ++ z)
    (h_pump_i₀ : u ++ v ^+^ i₀ ++ x ++ y ^+^ i₀ ++ z ∈ lang_neq_neq)
    (h_i₀_ge_2 : 2 ≤ i₀)
    {a b : Fin 3} (hab : a ≠ b) (hay : a ∈ y) (hby : b ∈ y) : False := by
      obtain ⟨ i, j, k, h ⟩ := h_pump_i₀;
      have h_chain_y : (y ^+^ i₀).Chain' (· ≤ ·) := by
        have h_chain_y : (u ++ v ^+^ i₀ ++ x ++ y ^+^ i₀ ++ z).Chain' (· ≤ ·) := by
          rw [ h.1 ] ; exact chain'_replicate_abc _ _ _;
        convert chain'_middle h_chain_y using 1;
      contrapose! h_chain_y;
      apply_rules [ nTimes_not_chain'_of_distinct ];
      · apply chain'_middle;
        convert h_split.symm ▸ chain'_replicate_abc ( 2 * n ) n ( 2 * n ) using 1;
      · use a, b

/-- `{a^i b^j c^k | i ≠ j ∧ j ≠ k}` is NOT context-free (provable by Ogden's lemma). -/
lemma not_CF_lang_neq_neq : ¬ is_CF lang_neq_neq := by
  intro hCF
  obtain ⟨p, hp⟩ := CF_ogdens_lemma hCF
  set n := p.factorial with hn_def
  set w := List.replicate (2 * n) (0 : Fin 3) ++ List.replicate n (1 : Fin 3) ++
           List.replicate (2 * n) (2 : Fin 3) with hw_def
  have hn_pos : 0 < n := Nat.factorial_pos p
  have hw_mem : w ∈ lang_neq_neq := ⟨2 * n, n, 2 * n, rfl, by omega, by omega⟩
  set P : ℕ → Prop := fun k => 2 * n ≤ k ∧ k < 2 * n + n with hP_def
  have hw_len : w.length = 2 * n + n + 2 * n := by simp [hw_def]; omega
  have h_marked : countMarkedIn P 0 w.length = n := by
    rw [hw_len]; exact countMarkedIn_middle_range (2 * n) n (2 * n)
  have h_p_le_n : p ≤ n := Nat.self_le_factorial p
  obtain ⟨u, v, x, y, z, h_split, h_vy_marked, h_vxy_marked, h_pump⟩ :=
    hp w hw_mem P (by omega)
  set α := List.count 0 v + List.count 0 y
  set β := List.count 1 v + List.count 1 y
  set γ := List.count 2 v + List.count 2 y
  have h_sum0 : List.count 0 u + List.count 0 x + List.count 0 z + α = 2 * n := by
    have := congr_arg (List.count (0 : Fin 3)) h_split
    simp [hw_def, List.count_append, List.count_replicate] at this; omega
  have h_sum1 : List.count 1 u + List.count 1 x + List.count 1 z + β = n := by
    have := congr_arg (List.count (1 : Fin 3)) h_split
    simp [hw_def, List.count_append, List.count_replicate] at this; omega
  have h_sum2 : List.count 2 u + List.count 2 x + List.count 2 z + γ = 2 * n := by
    have := congr_arg (List.count (2 : Fin 3)) h_split
    simp [hw_def, List.count_append, List.count_replicate] at this; omega
  have hβ_pos : 1 ≤ β := β_pos_of_vy_marked h_split hP_def h_vy_marked
  have hβ_le_p : β ≤ p := β_le_p_of_vxy_marked h_split hP_def h_vxy_marked
  have hβ_dvd : β ∣ n := Nat.dvd_factorial (by omega) (by omega)
  set i₀ := 1 + n / β
  have h_pump_i₀ := h_pump i₀
  have h_i₀_ge_2 : i₀ ≥ 2 := by
    simp only [i₀]; have := Nat.div_pos (Nat.le_of_dvd hn_pos hβ_dvd) hβ_pos; omega
  have h_count1_pump : List.count 1 (u ++ v ^+^ i₀ ++ x ++ y ^+^ i₀ ++ z) = 2 * n := by
    rw [pumped_count]
    have h_i₀_mul : i₀ * β = β + n := by
      simp only [i₀]; rw [Nat.add_mul, Nat.one_mul, Nat.div_mul_cancel hβ_dvd]
    simp only [β] at h_i₀_mul; omega
  have h_neq := lang_neq_neq_count h_pump_i₀
  -- If α = 0: count 0 of pumped = 2n = count 1 → contradiction
  -- If γ = 0: count 2 of pumped = 2n = count 1 → contradiction
  have hα_pos : 0 < α := by
    by_contra hα0; push_neg at hα0
    have h0 : List.count 0 (u ++ v ^+^ i₀ ++ x ++ y ^+^ i₀ ++ z) = 2 * n := by
      rw [pumped_count]; simp_all [α]
    have h_neq' := lang_neq_neq_count h_pump_i₀
    rw [h_count1_pump, h0] at h_neq'; exact absurd rfl h_neq'.1
  have hγ_pos : 0 < γ := by
    by_contra hγ0; push_neg at hγ0
    have h2 : List.count 2 (u ++ v ^+^ i₀ ++ x ++ y ^+^ i₀ ++ z) = 2 * n := by
      rw [pumped_count]; simp_all [γ]
    have h_neq' := lang_neq_neq_count h_pump_i₀
    rw [h_count1_pump, h2] at h_neq'; exact absurd rfl h_neq'.2
  obtain ⟨a, b, hab, hav, hbv⟩ | ⟨a, b, hab, hay, hby⟩ :=
    pigeonhole_three_symbols_fin3 (by omega) (by omega) (by omega)
  · exact sorted_pump_v_false h_split h_pump_i₀ h_i₀_ge_2 hab hav hbv
  · exact sorted_pump_y_false h_split h_pump_i₀ h_i₀_ge_2 hab hay hby

/-- `{aⁱ bʲ cᵏ | i = j ∨ j = k}` is NOT a deterministic context-free language. -/
theorem not_DCFL_lang_aibjck : ¬ is_DCFL lang_aibjck := by
  intro h_dcfl
  have h_compl_cf : is_CF lang_aibjckᶜ := is_CF_of_is_DCFL (is_DCFL_compl h_dcfl)
  have h_inter_cf : is_CF (lang_aibjckᶜ ⊓ lang_abc_star) :=
    CF_of_CF_inter_regular h_compl_cf isRegular_lang_abc_star
  rw [compl_aibjck_inter_abc_eq_neq_neq] at h_inter_cf
  exact not_CF_lang_neq_neq h_inter_cf

end explicit_witness
