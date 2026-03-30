import Grammars.Classes.ContextFree.Basics.Definition
import Grammars.Classes.ContextFree.Basics.Inclusion
import Grammars.Classes.ContextFree.Basics.Toolbox
import Grammars.Classes.ContextFree.Pumping.Pumping
import Grammars.Classes.ContextFree.Pumping.Utils
import Grammars.Utilities.ListUtils
import Mathlib

set_option maxHeartbeats 400000

/-! # Ogden's Lemma for Context-Free Languages

This file states and proves Ogden's lemma, a strengthened version of the pumping lemma
for context-free languages. While the pumping lemma guarantees that long enough strings
in a CFL can be "pumped", Ogden's lemma allows the user to *mark* certain positions of
the string and guarantees that the pump pieces contain marked positions.

## Main declarations

- `countMarkedIn` — counts how many positions in a range `[start, start + len)` are marked.
- `Language.IsContextFree.ogdens_lemma` — Ogden's lemma stated using Mathlib's `Language.IsContextFree`.
- `CF_ogdens_lemma` — Ogden's lemma stated using the project's `is_CF` predicate.

## Implementation notes

The proof follows the standard Ogden argument:
1. Convert to Chomsky Normal Form (CNF).
2. Navigate along the "marked path" to find a subtree with bounded marked height.
3. Use the pigeonhole principle on branching nonterminals to find a repeat.
4. The branching property ensures marked positions in the pump parts (v, y).
5. The bounded marked height ensures the marked-count bound on vxy.

The core technical lemma `ogdens_marked_path_decomp` implements the marked-path
pigeonhole argument. It tracks branching nonterminals in a finite set and detects
collisions to construct the Ogden decomposition.

## References

* William F. Ogden, "A Helpful Result for Proving Inherent Ambiguity",
  *Mathematical Systems Theory* **2** (1968), 191–194.
-/

open List

variable {T : Type}

/-! ## Counting marked positions -/

/-- Count how many natural numbers in the interval `[start, start + len)` satisfy `P`. -/
noncomputable def countMarkedIn (P : ℕ → Prop) [DecidablePred P] (start len : ℕ) : ℕ :=
  ((Finset.range len).filter (fun i => P (start + i))).card

@[simp]
lemma countMarkedIn_zero (P : ℕ → Prop) [DecidablePred P] (start : ℕ) :
    countMarkedIn P start 0 = 0 := by simp [countMarkedIn]

lemma countMarkedIn_le (P : ℕ → Prop) [DecidablePred P] (start len : ℕ) :
    countMarkedIn P start len ≤ len :=
  le_trans (Finset.card_filter_le _ _) (by simp)

lemma countMarkedIn_add (P : ℕ → Prop) [DecidablePred P] (start len₁ len₂ : ℕ) :
    countMarkedIn P start (len₁ + len₂) =
      countMarkedIn P start len₁ + countMarkedIn P (start + len₁) len₂ := by
  unfold countMarkedIn
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.sum_range_add]
  ac_rfl

lemma countMarkedIn_mono_len (P : ℕ → Prop) [DecidablePred P] (start : ℕ) {len₁ len₂ : ℕ}
    (h : len₁ ≤ len₂) : countMarkedIn P start len₁ ≤ countMarkedIn P start len₂ :=
  Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.range_mono h

/-! ## Parse tree marked count -/

namespace ChomskyNormalFormGrammar

universe uT uN

variable {T : Type uT} {g : ChomskyNormalFormGrammar.{uN, uT} T}

namespace parseTree

/-- The number of marked positions in a parse tree's yield. -/
noncomputable def mc (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    {n : g.NT} (t : parseTree n) : ℕ :=
  countMarkedIn P offset t.yield.length

lemma mc_node (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    {n c₁ c₂ : g.NT} (t₁ : parseTree c₁) (t₂ : parseTree c₂)
    (h : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules) :
    (parseTree.node t₁ t₂ h).mc P offset =
      t₁.mc P offset + t₂.mc P (offset + t₁.yield.length) := by
  simp only [mc, yield, List.length_append]
  exact countMarkedIn_add P offset t₁.yield.length t₂.yield.length

/-! ## Marked height -/

/-- The "marked branching depth": maximum number of branching points (where both
    children have marked descendants) on any root-to-leaf path. -/
noncomputable def markedHeight (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    {n : g.NT} : parseTree n → ℕ
  | leaf _ _ => 0
  | @node _ _ _ c₁ c₂ t₁ t₂ _ =>
    let mc₁ := t₁.mc P offset
    let mc₂ := t₂.mc P (offset + t₁.yield.length)
    if mc₁ > 0 ∧ mc₂ > 0 then
      max (t₁.markedHeight P offset) (t₂.markedHeight P (offset + t₁.yield.length)) + 1
    else if mc₁ > 0 then
      t₁.markedHeight P offset
    else
      t₂.markedHeight P (offset + t₁.yield.length)

/-! ## Key bounds -/

/-- mc ≤ 2^markedHeight -/
lemma mc_le_pow_markedHeight (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    {n : g.NT} (t : parseTree n) :
    t.mc P offset ≤ 2 ^ (t.markedHeight P offset) := by
  induction t generalizing offset with
  | leaf t₁ t₂ =>
    simp [mc, markedHeight]
    exact countMarkedIn_le P offset (leaf t₁ t₂).yield.length
  | node t₁ t₂ hnc ih₁ ih₂ =>
    rw [mc_node]
    show t₁.mc P offset + t₂.mc P (offset + t₁.yield.length) ≤
      2 ^ (markedHeight P offset (t₁.node t₂ hnc))
    rw [show markedHeight P offset (t₁.node t₂ hnc) =
      if t₁.mc P offset > 0 ∧ t₂.mc P (offset + t₁.yield.length) > 0 then
        max (t₁.markedHeight P offset) (t₂.markedHeight P (offset + t₁.yield.length)) + 1
      else if t₁.mc P offset > 0 then t₁.markedHeight P offset
      else t₂.markedHeight P (offset + t₁.yield.length) from rfl]
    split_ifs <;> simp_all [pow_succ']
    calc t₁.mc P offset + t₂.mc P (offset + t₁.yield.length)
        ≤ 2 ^ t₁.markedHeight P offset + 2 ^ t₂.markedHeight P (offset + t₁.yield.length) :=
          Nat.add_le_add (ih₁ _) (ih₂ _)
      _ ≤ 2 ^ max (t₁.markedHeight P offset) (t₂.markedHeight P (offset + t₁.yield.length)) +
          2 ^ max (t₁.markedHeight P offset) (t₂.markedHeight P (offset + t₁.yield.length)) :=
          Nat.add_le_add
            (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
            (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
      _ = _ := by ring

/-- 2^h ≤ mc → h ≤ markedHeight -/
lemma mc_implies_markedHeight (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    {n : g.NT} (t : parseTree n) (h : ℕ) (hmc : 2 ^ h ≤ t.mc P offset) :
    h ≤ t.markedHeight P offset := by
  have h_mc_le := mc_le_pow_markedHeight P offset t
  exact le_of_not_gt fun hlt => by linarith [pow_lt_pow_right₀ (by decide : 1 < 2) hlt]

/-- markedHeight ≤ height -/
lemma markedHeight_le_height (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    {n : g.NT} (t : parseTree n) :
    t.markedHeight P offset ≤ t.height := by
  induction t generalizing offset with
  | leaf => exact Nat.zero_le _
  | node t₁ t₂ _ ih₁ ih₂ =>
    unfold markedHeight height
    grind +ring

variable [DecidableEq g.NT] [DecidableEq (Σ _n : g.NT, parseTree _n)]

/-! ## Derivation helper lemmas -/

/-- From a derivation of the left child, build a derivation of the node. -/
lemma node_derives_left {n c₁ c₂ : g.NT} {t₂ : parseTree c₂}
    (hnc : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules)
    {u : List (Symbol T g.NT)}
    (h : g.Derives [Symbol.nonterminal c₁] u) :
    g.Derives [Symbol.nonterminal n] (u ++ t₂.yield.map Symbol.terminal) := by
  have h1 : g.Derives [Symbol.nonterminal n] ([Symbol.nonterminal c₁] ++ [Symbol.nonterminal c₂]) :=
    .single ⟨_, hnc, ChomskyNormalFormRule.Rewrites.input_output⟩
  have h2 : g.Derives ([Symbol.nonterminal c₁] ++ [Symbol.nonterminal c₂])
      (u ++ [Symbol.nonterminal c₂]) :=
    h.append_right _
  have h3 : g.Derives (u ++ [Symbol.nonterminal c₂])
      (u ++ t₂.yield.map Symbol.terminal) :=
    t₂.yield_derives.append_left _
  exact h1.trans (h2.trans h3)

/-- From a derivation of the right child, build a derivation of the node. -/
lemma node_derives_right {n c₁ c₂ : g.NT} {t₁ : parseTree c₁}
    (hnc : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules)
    {u : List (Symbol T g.NT)}
    (h : g.Derives [Symbol.nonterminal c₂] u) :
    g.Derives [Symbol.nonterminal n] (t₁.yield.map Symbol.terminal ++ u) := by
  have h1 : g.Derives [Symbol.nonterminal n] ([Symbol.nonterminal c₁] ++ [Symbol.nonterminal c₂]) :=
    .single ⟨_, hnc, ChomskyNormalFormRule.Rewrites.input_output⟩
  have h2 : g.Derives ([Symbol.nonterminal c₁] ++ [Symbol.nonterminal c₂])
      (t₁.yield.map Symbol.terminal ++ [Symbol.nonterminal c₂]) :=
    t₁.yield_derives.append_right _
  have h3 : g.Derives (t₁.yield.map Symbol.terminal ++ [Symbol.nonterminal c₂])
      (t₁.yield.map Symbol.terminal ++ u) :=
    h.append_left _
  exact h1.trans (h2.trans h3)

/-! ## Helper lemmas for extending Ogden results through nodes -/

/-
PROBLEM
Extend a Left Ogden result from the left child through a node.

PROVIDED SOLUTION
Take u' = u, v' = v, x' = x, y' = y, z' = z ++ t₂.yield.
- yield: (node t₁ t₂ hnc).yield = t₁.yield ++ t₂.yield = (u ++ v ++ x ++ y ++ z) ++ t₂.yield = u ++ v ++ x ++ y ++ (z ++ t₂.yield). Done by List.append_assoc.
- marked count: same offsets since u' = u, v' = v, etc. Direct from hmark.
- bound: same offsets. Direct from hbound.
- pump: For each i, hpump i gives g.Derives [c₁] ((u ++ v^+^i ++ x ++ y^+^i ++ z).map terminal). Apply node_derives_left hnc to get g.Derives [n] ((u ++ v^+^i ++ x ++ y^+^i ++ z).map terminal ++ t₂.yield.map terminal). Then rewrite: (u ++ v^+^i ++ x ++ y^+^i ++ z).map terminal ++ t₂.yield.map terminal = (u ++ v^+^i ++ x ++ y^+^i ++ (z ++ t₂.yield)).map terminal.
-/
lemma ogden_extend_left_via_left {n c₁ c₂ : g.NT}
    {t₁ : parseTree c₁} {t₂ : parseTree c₂}
    (hnc : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules)
    (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    {u v x y z : List T}
    (hyield : t₁.yield = u ++ v ++ x ++ y ++ z)
    (hmark : 0 < countMarkedIn P (offset + u.length) v.length +
        countMarkedIn P (offset + u.length + v.length + x.length) y.length)
    (hbound : countMarkedIn P (offset + u.length) (v.length + x.length + y.length) ≤
        2 ^ g.generators.card)
    (hpump : ∀ i : ℕ, g.Derives [Symbol.nonterminal c₁]
        ((u ++ v ^+^ i ++ x ++ y ^+^ i ++ z).map Symbol.terminal)) :
    ∃ u' v' x' y' z' : List T,
      (parseTree.node t₁ t₂ hnc).yield = u' ++ v' ++ x' ++ y' ++ z' ∧
      0 < countMarkedIn P (offset + u'.length) v'.length +
          countMarkedIn P (offset + u'.length + v'.length + x'.length) y'.length ∧
      countMarkedIn P (offset + u'.length) (v'.length + x'.length + y'.length) ≤
          2 ^ g.generators.card ∧
      ∀ i : ℕ, g.Derives [Symbol.nonterminal n]
        ((u' ++ v' ^+^ i ++ x' ++ y' ^+^ i ++ z').map Symbol.terminal) := by
  refine' ⟨ u, v, x, y, z ++ t₂.yield, _, _, _, _ ⟩ <;> simp_all +decide [ List.append_assoc ];
  · unfold parseTree.yield; aesop;
  · intro i
    specialize hpump i
    generalize_proofs at *; (
    convert ChomskyNormalFormGrammar.parseTree.node_derives_left hnc hpump using 1 ; simp +decide [ List.append_assoc ];
    convert rfl using 1)

/-
PROBLEM
Extend a Left Ogden result from the right child through a node.

PROVIDED SOLUTION
Take u' = t₁.yield ++ u, v' = v, x' = x, y' = y, z' = z.
- yield: (node t₁ t₂ hnc).yield = t₁.yield ++ t₂.yield = t₁.yield ++ (u ++ v ++ x ++ y ++ z) = (t₁.yield ++ u) ++ v ++ x ++ y ++ z.
- marked count: offset + u'.length = offset + t₁.yield.length + u.length. Same as hmark.
- bound: same.
- pump: For each i, hpump i gives g.Derives [c₂] ((u ++ v^+^i ++ x ++ y^+^i ++ z).map terminal). Apply node_derives_right hnc to get g.Derives [n] (t₁.yield.map terminal ++ (u ++ v^+^i ++ x ++ y^+^i ++ z).map terminal). Then rewrite: = ((t₁.yield ++ u) ++ v^+^i ++ x ++ y^+^i ++ z).map terminal.
-/
lemma ogden_extend_left_via_right {n c₁ c₂ : g.NT}
    {t₁ : parseTree c₁} {t₂ : parseTree c₂}
    (hnc : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules)
    (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    {u v x y z : List T}
    (hyield : t₂.yield = u ++ v ++ x ++ y ++ z)
    (hmark : 0 < countMarkedIn P (offset + t₁.yield.length + u.length) v.length +
        countMarkedIn P (offset + t₁.yield.length + u.length + v.length + x.length) y.length)
    (hbound : countMarkedIn P (offset + t₁.yield.length + u.length)
        (v.length + x.length + y.length) ≤ 2 ^ g.generators.card)
    (hpump : ∀ i : ℕ, g.Derives [Symbol.nonterminal c₂]
        ((u ++ v ^+^ i ++ x ++ y ^+^ i ++ z).map Symbol.terminal)) :
    ∃ u' v' x' y' z' : List T,
      (parseTree.node t₁ t₂ hnc).yield = u' ++ v' ++ x' ++ y' ++ z' ∧
      0 < countMarkedIn P (offset + u'.length) v'.length +
          countMarkedIn P (offset + u'.length + v'.length + x'.length) y'.length ∧
      countMarkedIn P (offset + u'.length) (v'.length + x'.length + y'.length) ≤
          2 ^ g.generators.card ∧
      ∀ i : ℕ, g.Derives [Symbol.nonterminal n]
        ((u' ++ v' ^+^ i ++ x' ++ y' ^+^ i ++ z').map Symbol.terminal) := by
  refine' ⟨ t₁.yield ++ u, v, x, y, z, _, _, _, _ ⟩ <;> simp_all +decide [ List.length_append, nTimes ];
  · exact hyield ▸ rfl;
  · simpa only [ add_assoc ] using hmark;
  · simpa only [ add_assoc ] using hbound;
  · intro i;
    convert node_derives_right hnc ( hpump i ) using 1

/-
PROBLEM
Extend a Right Ogden result from the left child through a node.

PROVIDED SOLUTION
Take n'' = n', p'' = p', u₂ = u₁, z₂ = z₁ ++ t₂.yield.
- yield: (node t₁ t₂ hnc).yield = t₁.yield ++ t₂.yield = (u₁ ++ p'.yield ++ z₁) ++ t₂.yield = u₁ ++ p'.yield ++ (z₁ ++ t₂.yield).
- mc: p''.mc P (offset + u₂.length) = p'.mc P (offset + u₁.length) > 0. Direct.
- derives: Apply node_derives_left hnc to hderiv: g.Derives [n] ((u₁.map terminal ++ [nonterminal n'] ++ z₁.map terminal) ++ t₂.yield.map terminal). Rewrite = u₁.map terminal ++ [nonterminal n'] ++ (z₁ ++ t₂.yield).map terminal.
-/
lemma ogden_extend_right_via_left {n c₁ c₂ : g.NT}
    {t₁ : parseTree c₁} {t₂ : parseTree c₂}
    (hnc : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules)
    (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    (s : Finset g.NT)
    {n' : g.NT} (hn's : n' ∈ s)
    {p' : parseTree n'} {u₁ z₁ : List T}
    (hyield : t₁.yield = u₁ ++ p'.yield ++ z₁)
    (hmc' : 0 < p'.mc P (offset + u₁.length))
    (hderiv : g.Derives [Symbol.nonterminal c₁]
        (u₁.map Symbol.terminal ++ [Symbol.nonterminal n'] ++ z₁.map Symbol.terminal)) :
    ∃ n'' ∈ s, ∃ (p'' : parseTree n'') (u₂ z₂ : List T),
      (parseTree.node t₁ t₂ hnc).yield = u₂ ++ p''.yield ++ z₂ ∧
      0 < p''.mc P (offset + u₂.length) ∧
      g.Derives [Symbol.nonterminal n]
        (u₂.map Symbol.terminal ++ [Symbol.nonterminal n''] ++ z₂.map Symbol.terminal) := by
  use n', hn's, p', u₁, z₁ ++ t₂.yield.map (fun x => x);
  refine' ⟨ _, hmc', _ ⟩;
  · simp +decide [ hyield, parseTree.yield ];
  · convert node_derives_left hnc hderiv using 1 ; simp +decide [ *, List.map_append ];
    congr! 1

/-
PROBLEM
Extend a Right Ogden result from the right child through a node.

PROVIDED SOLUTION
Take n'' = n', p'' = p', u₂ = t₁.yield ++ u₁, z₂ = z₁.
- yield: (node t₁ t₂ hnc).yield = t₁.yield ++ t₂.yield = t₁.yield ++ (u₁ ++ p'.yield ++ z₁) = (t₁.yield ++ u₁) ++ p'.yield ++ z₁.
- mc: p''.mc P (offset + u₂.length) = p'.mc P (offset + t₁.yield.length + u₁.length) > 0.
- derives: Apply node_derives_right hnc to hderiv: g.Derives [n] (t₁.yield.map terminal ++ (u₁.map terminal ++ [nonterminal n'] ++ z₁.map terminal)). Rewrite = (t₁.yield ++ u₁).map terminal ++ [nonterminal n'] ++ z₁.map terminal.
-/
lemma ogden_extend_right_via_right {n c₁ c₂ : g.NT}
    {t₁ : parseTree c₁} {t₂ : parseTree c₂}
    (hnc : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules)
    (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    (s : Finset g.NT)
    {n' : g.NT} (hn's : n' ∈ s)
    {p' : parseTree n'} {u₁ z₁ : List T}
    (hyield : t₂.yield = u₁ ++ p'.yield ++ z₁)
    (hmc' : 0 < p'.mc P (offset + t₁.yield.length + u₁.length))
    (hderiv : g.Derives [Symbol.nonterminal c₂]
        (u₁.map Symbol.terminal ++ [Symbol.nonterminal n'] ++ z₁.map Symbol.terminal)) :
    ∃ n'' ∈ s, ∃ (p'' : parseTree n'') (u₂ z₂ : List T),
      (parseTree.node t₁ t₂ hnc).yield = u₂ ++ p''.yield ++ z₂ ∧
      0 < p''.mc P (offset + u₂.length) ∧
      g.Derives [Symbol.nonterminal n]
        (u₂.map Symbol.terminal ++ [Symbol.nonterminal n''] ++ z₂.map Symbol.terminal) := by
  use n';
  refine' ⟨ hn's, p', t₁.yield ++ u₁, z₁, _, _, _ ⟩;
  · simp +decide [ hyield, parseTree.yield ];
  · simpa [ add_assoc, List.length_append ] using hmc';
  · convert node_derives_right hnc hderiv using 1 ; simp +decide [ *, List.map_append ];
    congr! 1

/-
PROBLEM
Construct an Ogden Left result from a collision with n in the left child,
    when both children have marked positions (branching node).

PROVIDED SOLUTION
Take u = [], v = u₁, x = p'.yield, y = z₁ ++ t₂.yield, z = [].

Yield: (node t₁ t₂ hnc).yield = t₁.yield ++ t₂.yield = (u₁ ++ p'.yield ++ z₁) ++ t₂.yield = [] ++ u₁ ++ p'.yield ++ (z₁ ++ t₂.yield) ++ [].

Marked count: We need 0 < countMarkedIn P (offset + 0) u₁.length + countMarkedIn P (offset + u₁.length + p'.yield.length) (z₁ ++ t₂.yield).length.
The second term counts marked positions in z₁ ++ t₂.yield at the correct offset.
Note: offset + u₁.length + p'.yield.length = offset + (u₁ ++ p'.yield).length, and (z₁ ++ t₂.yield) starts at offset + u₁.length + p'.yield.length.
By countMarkedIn_add, countMarkedIn on z₁ ++ t₂.yield = countMarkedIn on z₁ + countMarkedIn on t₂.yield.
Since t₂.mc P (offset + t₁.yield.length) > 0 (by hmc₂), and t₁.yield = u₁ ++ p'.yield ++ z₁, we have t₁.yield.length = u₁.length + p'.yield.length + z₁.length. So the t₂ marked count starts at offset + u₁.length + p'.yield.length + z₁.length. This is exactly countMarkedIn P (offset + u₁.length + p'.yield.length + z₁.length) t₂.yield.length > 0. So the total on y is ≥ countMarkedIn on t₂.yield > 0.

Bound: countMarkedIn P offset (u₁.length + p'.yield.length + (z₁ ++ t₂.yield).length) = countMarkedIn P offset (t₁.yield.length + t₂.yield.length) = mc(node t₁ t₂ hnc) ≤ 2^generators.card.

Pump: From hderiv₁, g.Derives [c₁] (u₁.map terminal ++ [nonterminal n] ++ z₁.map terminal).
By node_derives_left hnc: g.Derives [n] (u₁.map terminal ++ [nonterminal n] ++ z₁.map terminal ++ t₂.yield.map terminal).
Rewrite: = u₁.map terminal ++ [nonterminal n] ++ (z₁ ++ t₂.yield).map terminal.

So g.Derives [nonterminal n] (u₁.map terminal ++ [nonterminal n] ++ (z₁ ++ t₂.yield).map terminal).

By pumping_string, for each i: g.Derives [n] (u₁^+^i.map terminal ++ [nonterminal n] ++ (z₁ ++ t₂.yield)^+^i.map terminal).

Then compose with p'.yield_derives (g.Derives [n] (p'.yield.map terminal)):
g.Derives [n] (u₁^+^i.map terminal ++ p'.yield.map terminal ++ (z₁ ++ t₂.yield)^+^i.map terminal).

Rewrite: = ([] ++ u₁^+^i ++ p'.yield ++ (z₁ ++ t₂.yield)^+^i ++ []).map terminal.

Use the Derives.append_left and Derives.append_right to compose.

Actually, more precisely: pumping_string gives Derives on lists of Symbol (mixed terminal/nonterminal). From pumping_string we get:
g.Derives [nonterminal n] (u₁.map terminal ^+^ i ++ [nonterminal n] ++ (z₁ ++ t₂.yield).map terminal ^+^ i)

Then use Derives.trans with (Derives.append_left p'.yield_derives (u₁.map terminal ^+^ i)).append_right ((z₁ ++ t₂.yield).map terminal ^+^ i).

And use nTimes_map to rewrite u₁.map terminal ^+^ i = (u₁ ^+^ i).map terminal, etc.
-/
lemma ogden_pump_from_left {n c₁ c₂ : g.NT}
    {t₁ : parseTree c₁} {t₂ : parseTree c₂}
    (hnc : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules)
    (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    (hmc₂ : 0 < t₂.mc P (offset + t₁.yield.length))
    (hmc_bound : (parseTree.node t₁ t₂ hnc).mc P offset ≤ 2 ^ g.generators.card)
    {p' : parseTree n} {u₁ z₁ : List T}
    (hyield₁ : t₁.yield = u₁ ++ p'.yield ++ z₁)
    (hmc' : 0 < p'.mc P (offset + u₁.length))
    (hderiv₁ : g.Derives [Symbol.nonterminal c₁]
        (u₁.map Symbol.terminal ++ [Symbol.nonterminal n] ++ z₁.map Symbol.terminal)) :
    ∃ u v x y z : List T,
      (parseTree.node t₁ t₂ hnc).yield = u ++ v ++ x ++ y ++ z ∧
      0 < countMarkedIn P (offset + u.length) v.length +
          countMarkedIn P (offset + u.length + v.length + x.length) y.length ∧
      countMarkedIn P (offset + u.length) (v.length + x.length + y.length) ≤
          2 ^ g.generators.card ∧
      ∀ i : ℕ, g.Derives [Symbol.nonterminal n]
        ((u ++ v ^+^ i ++ x ++ y ^+^ i ++ z).map Symbol.terminal) := by
  refine' ⟨ [ ], u₁, p'.yield, z₁ ++ t₂.yield, [ ], _, _, _, _ ⟩ <;> simp_all +decide [ Finset.card_range ];
  · simp [parseTree.yield, hyield₁];
  · contrapose! hmc₂; simp_all +decide [ add_assoc, countMarkedIn_add ] ;
    exact hmc₂.2.2;
  · unfold mc at hmc_bound; simp_all +decide [ countMarkedIn ] ;
    convert hmc_bound using 3 ; simp +decide [ *, ChomskyNormalFormGrammar.parseTree.yield ] ; ring!;
  · intro i
    have h_deriv : g.Derives [Symbol.nonterminal n] (map Symbol.terminal (u₁ ^+^ i) ++ [Symbol.nonterminal n] ++ map Symbol.terminal ((z₁ ++ t₂.yield) ^+^ i)) := by
      convert pumping_string _ i using 1;
      rotate_left;
      exact u₁.map Symbol.terminal
      exact ( z₁ ++ t₂.yield ).map Symbol.terminal
      generalize_proofs at *; (
      convert node_derives_left hnc hderiv₁ using 1 ; simp +decide [ hyield₁ ];
      congr! 1);
      exact congr_arg₂ _ ( congr_arg₂ _ ( by exact? ) rfl ) ( by exact? );
    grind +suggestions

/-
PROBLEM
Construct an Ogden Left result from a collision with n in the right child,
    when both children have marked positions (branching node).

PROVIDED SOLUTION
Take u = [], v = t₁.yield ++ u₁, x = p'.yield, y = z₁, z = [].

Yield: (node t₁ t₂ hnc).yield = t₁.yield ++ t₂.yield = t₁.yield ++ (u₁ ++ p'.yield ++ z₁) = [] ++ (t₁.yield ++ u₁) ++ p'.yield ++ z₁ ++ [].

Marked count: We need 0 < countMarkedIn P offset (t₁.yield ++ u₁).length + countMarkedIn P (offset + (t₁.yield ++ u₁).length + p'.yield.length) z₁.length.
The first term counts marked positions in t₁.yield ++ u₁. Since hmc₁ > 0, t₁.mc P offset > 0 means countMarkedIn P offset t₁.yield.length > 0. Since (t₁.yield ++ u₁).length ≥ t₁.yield.length, by countMarkedIn_mono_len, countMarkedIn P offset (t₁.yield ++ u₁).length ≥ countMarkedIn P offset t₁.yield.length > 0.

Bound: countMarkedIn P offset ((t₁.yield ++ u₁).length + p'.yield.length + z₁.length) = countMarkedIn P offset (t₁.yield.length + t₂.yield.length) = mc(node t₁ t₂ hnc) ≤ 2^generators.card.

Pump: From hderiv₂, g.Derives [c₂] (u₁.map terminal ++ [nonterminal n] ++ z₁.map terminal).
By node_derives_right hnc: g.Derives [n] (t₁.yield.map terminal ++ (u₁.map terminal ++ [nonterminal n] ++ z₁.map terminal)).
Rewrite: = (t₁.yield ++ u₁).map terminal ++ [nonterminal n] ++ z₁.map terminal.

By pumping_string, for each i: g.Derives [n] ((t₁.yield ++ u₁).map terminal ^+^ i ++ [nonterminal n] ++ z₁.map terminal ^+^ i).
Then compose with p'.yield_derives using append_left/right.
Use nTimes_map to convert.
-/
lemma ogden_pump_from_right {n c₁ c₂ : g.NT}
    {t₁ : parseTree c₁} {t₂ : parseTree c₂}
    (hnc : (ChomskyNormalFormRule.node n c₁ c₂) ∈ g.rules)
    (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    (hmc₁ : 0 < t₁.mc P offset)
    (hmc_bound : (parseTree.node t₁ t₂ hnc).mc P offset ≤ 2 ^ g.generators.card)
    {p' : parseTree n} {u₁ z₁ : List T}
    (hyield₂ : t₂.yield = u₁ ++ p'.yield ++ z₁)
    (hmc' : 0 < p'.mc P (offset + t₁.yield.length + u₁.length))
    (hderiv₂ : g.Derives [Symbol.nonterminal c₂]
        (u₁.map Symbol.terminal ++ [Symbol.nonterminal n] ++ z₁.map Symbol.terminal)) :
    ∃ u v x y z : List T,
      (parseTree.node t₁ t₂ hnc).yield = u ++ v ++ x ++ y ++ z ∧
      0 < countMarkedIn P (offset + u.length) v.length +
          countMarkedIn P (offset + u.length + v.length + x.length) y.length ∧
      countMarkedIn P (offset + u.length) (v.length + x.length + y.length) ≤
          2 ^ g.generators.card ∧
      ∀ i : ℕ, g.Derives [Symbol.nonterminal n]
        ((u ++ v ^+^ i ++ x ++ y ^+^ i ++ z).map Symbol.terminal) := by
  by_contra h_contra;
  refine' h_contra ⟨ [ ], t₁.yield ++ u₁, p'.yield, z₁, [ ], _, _, _, _ ⟩ <;> simp +decide [ * ];
  · simp +decide [ hyield₂, parseTree.yield ];
  · refine' Or.inl ( lt_of_lt_of_le hmc₁ _ );
    apply_rules [ countMarkedIn_mono_len ] ; simp +decide [ * ] ;
  · convert hmc_bound using 1;
    unfold mc; simp +decide [ *, add_assoc ] ;
    rw [ show ( t₁.node t₂ hnc ).yield = t₁.yield ++ t₂.yield from rfl, hyield₂ ] ; simp +decide [ add_assoc ] ;
  · intro i
    have h_pump : g.Derives [Symbol.nonterminal n] ((t₁.yield ++ u₁).map Symbol.terminal ^+^ i ++ [Symbol.nonterminal n] ++ (z₁.map Symbol.terminal) ^+^ i) := by
      have h_deriv : g.Derives [Symbol.nonterminal n] ((t₁.yield ++ u₁).map Symbol.terminal ++ [Symbol.nonterminal n] ++ (z₁.map Symbol.terminal)) := by
        convert ChomskyNormalFormGrammar.parseTree.node_derives_right hnc _ using 1 ; aesop;
        simpa using hderiv₂;
      have h_pump : ∀ i : ℕ, g.Derives [Symbol.nonterminal n] ((t₁.yield ++ u₁).map Symbol.terminal ^+^ i ++ [Symbol.nonterminal n] ++ (z₁.map Symbol.terminal) ^+^ i) := by
        intro i
        have := h_deriv
        exact?
      generalize_proofs at *;
      exact h_pump i
    generalize_proofs at *;
    grind +suggestions

/-! ## Core Ogden marked-path pigeonhole -/

lemma ogdens_marked_path_decomp {n : g.NT} (p : parseTree n)
    (P : ℕ → Prop) [DecidablePred P] (offset : ℕ)
    (s : Finset g.NT) (hs_sub : s ⊆ g.generators)
    (hp : g.generators.card ≤ p.markedHeight P offset + s.card)
    (hmc : 0 < p.mc P offset)
    (hmc_bound : p.mc P offset ≤ 2 ^ g.generators.card) :
    (∃ u v x y z : List T,
      p.yield = u ++ v ++ x ++ y ++ z ∧
      0 < countMarkedIn P (offset + u.length) v.length +
          countMarkedIn P (offset + u.length + v.length + x.length) y.length ∧
      countMarkedIn P (offset + u.length) (v.length + x.length + y.length) ≤
          2 ^ g.generators.card ∧
      ∀ i : ℕ, g.Derives [Symbol.nonterminal n]
        ((u ++ v ^+^ i ++ x ++ y ^+^ i ++ z).map Symbol.terminal)) ∨
    (∃ n' ∈ s, ∃ (p' : parseTree n') (u₁ z₁ : List T),
      p.yield = u₁ ++ p'.yield ++ z₁ ∧
      0 < p'.mc P (offset + u₁.length) ∧
      g.Derives [Symbol.nonterminal n]
        (u₁.map Symbol.terminal ++ [Symbol.nonterminal n'] ++ z₁.map Symbol.terminal)) := by
  induction p generalizing offset s with
  | @leaf n t hnt =>
    simp only [markedHeight] at hp
    have hs_eq : s = g.generators := (Finset.subset_iff_eq_of_card_le (by omega)).mp hs_sub
    have hn_gen : n ∈ g.generators := input_mem_generators hnt
    have hn_s : n ∈ s := hs_eq ▸ hn_gen
    right
    refine ⟨n, hn_s, leaf t hnt, [], [], ?_, ?_, ?_⟩
    · simp [yield]
    · simpa using hmc
    · simp; exact Derives.refl _
  | @node n c₁ c₂ t₁ t₂ hnc ih₁ ih₂ =>
    have hmc_eq := mc_node P offset t₁ t₂ hnc
    by_cases h₁ : (0 : ℕ) < t₁.mc P offset <;> by_cases h₂ : (0 : ℕ) < t₂.mc P (offset + t₁.yield.length)
    · -- Case A: both children have mc > 0
      have hmh : markedHeight P offset (node t₁ t₂ hnc) =
          max (t₁.markedHeight P offset) (t₂.markedHeight P (offset + t₁.yield.length)) + 1 := by
        show (let mc₁ := _; let mc₂ := _; if mc₁ > 0 ∧ mc₂ > 0 then _ else _) = _
        simp [h₁, h₂]
      rw [hmh] at hp
      by_cases hns : n ∈ s
      · right
        refine ⟨n, hns, node t₁ t₂ hnc, [], [], ?_, ?_, ?_⟩
        · simp [yield]
        · simpa using hmc
        · simp; exact Derives.refl _
      · have hn_gen : n ∈ g.generators := input_mem_generators hnc
        have hs'_sub : insert n s ⊆ g.generators := Finset.insert_subset hn_gen hs_sub
        have hs'_card : (insert n s).card = s.card + 1 := by
          rw [Finset.card_insert_eq_ite, if_neg hns]
        by_cases hmh_le : t₂.markedHeight P (offset + t₁.yield.length) ≤ t₁.markedHeight P offset
        · -- recurse left
          have hp₁ : g.generators.card ≤ t₁.markedHeight P offset + (insert n s).card := by
            simp only [Nat.max_eq_left hmh_le] at hp; omega
          have hmc₁_bnd : t₁.mc P offset ≤ (2 : ℕ) ^ g.generators.card := by omega
          rcases ih₁ offset (insert n s) hs'_sub hp₁ h₁ hmc₁_bnd with h_l | h_r
          · obtain ⟨u, v, x, y, z, hy, hm, hb, hd⟩ := h_l
            exact Or.inl (ogden_extend_left_via_left hnc P offset hy hm hb hd)
          · obtain ⟨n', hn', p', u₁', z₁', hy, hmc'', hd⟩ := h_r
            have h_or : n' = n ∨ n' ∈ s := Finset.mem_insert.mp hn'
            rcases h_or with h_eq | hn's
            · subst h_eq
              exact Or.inl (ogden_pump_from_left hnc P offset h₂ hmc_bound hy hmc'' hd)
            · exact Or.inr (ogden_extend_right_via_left hnc P offset s hn's hy hmc'' hd)
        · -- recurse right
          push_neg at hmh_le
          have hp₂ : g.generators.card ≤ t₂.markedHeight P (offset + t₁.yield.length) + (insert n s).card := by
            have := Nat.le_max_right (t₁.markedHeight P offset) (t₂.markedHeight P (offset + t₁.yield.length))
            omega
          have hmc₂_bnd : t₂.mc P (offset + t₁.yield.length) ≤ (2 : ℕ) ^ g.generators.card := by omega
          rcases ih₂ (offset + t₁.yield.length) (insert n s) hs'_sub hp₂ h₂ hmc₂_bnd with h_l | h_r
          · obtain ⟨u, v, x, y, z, hy, hm, hb, hd⟩ := h_l
            exact Or.inl (ogden_extend_left_via_right hnc P offset hy hm hb hd)
          · obtain ⟨n', hn', p', u₁', z₁', hy, hmc'', hd⟩ := h_r
            have h_or : n' = n ∨ n' ∈ s := Finset.mem_insert.mp hn'
            rcases h_or with h_eq | hn's
            · subst h_eq
              exact Or.inl (ogden_pump_from_right hnc P offset h₁ hmc_bound hy hmc'' hd)
            · exact Or.inr (ogden_extend_right_via_right hnc P offset s hn's hy hmc'' hd)
    · -- Case B: only left child has mc > 0
      simp only [not_lt, Nat.le_zero] at h₂
      have hmh : markedHeight P offset (node t₁ t₂ hnc) = t₁.markedHeight P offset := by
        show (let mc₁ := _; let mc₂ := _; if mc₁ > 0 ∧ mc₂ > 0 then _ else _) = _
        simp [h₁, h₂]
      rw [hmh] at hp
      have hmc₁_bnd : t₁.mc P offset ≤ (2 : ℕ) ^ g.generators.card := by omega
      rcases ih₁ offset s hs_sub hp h₁ hmc₁_bnd with h_l | h_r
      · obtain ⟨u, v, x, y, z, hy, hm, hb, hd⟩ := h_l
        exact Or.inl (ogden_extend_left_via_left hnc P offset hy hm hb hd)
      · obtain ⟨n', hn', p', u₁', z₁', hy, hmc'', hd⟩ := h_r
        exact Or.inr (ogden_extend_right_via_left hnc P offset s hn' hy hmc'' hd)
    · -- Case C: only right child has mc > 0
      simp only [not_lt, Nat.le_zero] at h₁
      have hmh : markedHeight P offset (node t₁ t₂ hnc) =
          t₂.markedHeight P (offset + t₁.yield.length) := by
        show (let mc₁ := _; let mc₂ := _; if mc₁ > 0 ∧ mc₂ > 0 then _ else _) = _
        simp [h₁, h₂]
      rw [hmh] at hp
      have hmc₂_bnd : t₂.mc P (offset + t₁.yield.length) ≤ (2 : ℕ) ^ g.generators.card := by omega
      rcases ih₂ (offset + t₁.yield.length) s hs_sub hp h₂ hmc₂_bnd with h_l | h_r
      · obtain ⟨u, v, x, y, z, hy, hm, hb, hd⟩ := h_l
        exact Or.inl (ogden_extend_left_via_right hnc P offset hy hm hb hd)
      · obtain ⟨n', hn', p', u₁', z₁', hy, hmc'', hd⟩ := h_r
        exact Or.inr (ogden_extend_right_via_right hnc P offset s hn' hy hmc'' hd)
    · -- Case D: neither child has mc > 0, contradiction
      simp only [not_lt, Nat.le_zero] at h₁ h₂
      omega

/-! ## Navigation to bounded-markedHeight subtree -/

/-
PROBLEM
Navigate along the marked path to find a subtree with `markedHeight = k`.

PROVIDED SOLUTION
By induction on the parse tree `p`.

Base case (leaf): markedHeight of a leaf is 0, so k = 0 and the tree itself works (with u₀ = z₀ = []).

Inductive case (node t₁ t₂ hnc): We have p = node t₁ t₂ hnc.
Since hmc > 0, at least one child has mc > 0.

Look at markedHeight of the node. It's defined by cases:
- If both children have mc > 0, markedHeight = max(mh₁, mh₂) + 1
- If only left has mc > 0, markedHeight = mh₁
- If only right has mc > 0, markedHeight = mh₂

Case 1: Both children have mc > 0. Then markedHeight(p) = max(mh₁, mh₂) + 1.
  If k = 0: Take the tree p itself with u₀ = z₀ = []. But we need mh = k = 0, which would need max(mh₁,mh₂)+1 = 0, impossible.
  Actually wait, if k ≤ markedHeight(p), and k = 0, we need to find a subtree with mh = 0. We can recurse deeper.

  Actually, let me think more carefully. If k ≤ max(mh₁, mh₂) + 1:
  - If k = max(mh₁, mh₂) + 1 = markedHeight(p), take the whole tree p itself.
  - If k ≤ max(mh₁, mh₂), WLOG mh₁ ≥ mh₂ (so max = mh₁). Then k ≤ mh₁.
    Since mc₁ > 0, apply IH to t₁. Get some subtree q of t₁ with markedHeight = k.
    Then yield(p) = yield(t₁) ++ yield(t₂), and yield(t₁) = u₀ ++ yield(q) ++ z₀.
    So yield(p) = u₀ ++ yield(q) ++ (z₀ ++ yield(t₂)), and the derivation extends via node_derives_left.

Case 2: Only left child has mc > 0. Then markedHeight(p) = mh₁.
  Apply IH to t₁. Get subtree. Extend with right child yield.

Case 3: Only right child has mc > 0. Then markedHeight(p) = mh₂.
  Apply IH to t₂. Get subtree. Extend with left child yield.

For the derivation part, use `node_derives_left` or `node_derives_right` composed with the IH derivation.

Actually, let me simplify the approach. The key insight is:

If k = markedHeight(p), take q = p, u₀ = z₀ = []. This trivially works.

If k < markedHeight(p), then p must be a node (since leaf has markedHeight 0, and if k < 0 that's impossible).
For a node:
- Follow the "marked path" to the child with higher markedHeight (or the one with mc > 0).
- Recurse into that child.
- Extend u₀ and z₀ appropriately.

This gives a straightforward structural induction.
-/
lemma ogdens_restrict_mh {n : g.NT} (p : parseTree n)
    (P : ℕ → Prop) [DecidablePred P] (offset : ℕ) (k : ℕ)
    (hmh : k ≤ p.markedHeight P offset) (hmc : 0 < p.mc P offset) :
    ∃ (n' : g.NT) (q : parseTree n') (u₀ z₀ : List T),
      p.yield = u₀ ++ q.yield ++ z₀ ∧
      q.markedHeight P (offset + u₀.length) = k ∧
      0 < q.mc P (offset + u₀.length) ∧
      g.Derives [Symbol.nonterminal n]
        (u₀.map Symbol.terminal ++ [Symbol.nonterminal n'] ++ z₀.map Symbol.terminal) := by
  by_contra! h_contra;
  induction' p with _ _ _ _ ih generalizing offset k;
  · unfold markedHeight at *; simp_all +decide [ List.length ] ;
    specialize h_contra _ ( leaf ‹_› ‹_› ) [ ] [ ] ; simp_all +decide [ List.length ];
    exact h_contra ( Relation.ReflTransGen.refl );
  · rename_i t₁ t₂ hnc ih₁ ih₂;
    by_cases h₁ : 0 < mc P offset t₁ <;> by_cases h₂ : 0 < mc P (offset + t₁.yield.length) t₂ <;> simp +decide [ *, markedHeight ] at hmh hmc ⊢;
    · by_cases hk : k ≤ max (markedHeight P offset t₁) (markedHeight P (offset + t₁.yield.length) t₂);
      · by_cases hk₁ : k ≤ markedHeight P offset t₁;
        · specialize ih₁ offset k hk₁ h₁;
          refine' ih₁ fun n' q u₀ z₀ h₁ h₂ h₃ h₄ => h_contra n' q u₀ ( z₀ ++ t₂.yield ) _ _ _ _;
          · simp +decide [ *, parseTree.yield ];
          · exact h₂;
          · exact h₃;
          · convert node_derives_left hnc h₄ using 1;
            any_goals exact t₂;
            simp +decide [ List.map_append ];
        · specialize ih₂ ( offset + t₁.yield.length ) ( k ) ( by
            grind +qlia ) h₂
          generalize_proofs at *; (
          simp +zetaDelta at *;
          obtain ⟨ n', q, u₀, z₀, h₁, h₂, h₃, h₄ ⟩ := ih₂; specialize h_contra n' q ( t₁.yield ++ u₀ ) z₀; simp_all +decide [ parseTree.yield ] ;
          simp_all +decide [ add_assoc ];
          exact h_contra ( by simpa [ ← List.append_assoc ] using node_derives_right hnc h₄ ));
      · specialize h_contra _ ( t₁.node t₂ hnc ) [ ] [ ] ; simp_all +decide [ parseTree.yield ];
        exact h_contra ( by rw [ show markedHeight P offset ( t₁.node t₂ hnc ) = max ( markedHeight P offset t₁ ) ( markedHeight P ( offset + t₁.yield.length ) t₂ ) + 1 from by rw [ markedHeight ] ; aesop ] ; omega ) ( Relation.ReflTransGen.refl );
    · specialize ih₁ offset k hmh h₁;
      refine' ih₁ fun n' q u₀ z₀ h₁ h₂ h₃ h₄ => h_contra n' q u₀ ( z₀ ++ t₂.yield ) _ _ _ _;
      · simp +decide [ h₁, parseTree.yield ];
      · exact h₂;
      · exact h₃;
      · convert ChomskyNormalFormGrammar.parseTree.node_derives_left hnc h₄ using 1 ; simp +decide [ h₁, List.map_append ];
        all_goals tauto;
    · specialize ih₂ ( offset + t₁.yield.length ) k hmh h₂;
      contrapose! ih₂; simp_all +decide [ markedHeight ] ;
      intro n' q u₀ z₀ h₁ h₂ h₃ h₄; specialize h_contra n' q ( t₁.yield ++ u₀ ) z₀; simp_all +decide [ parseTree.yield ] ;
      simp_all +decide [ add_assoc ];
      exact h_contra ( by simpa [ ← List.append_assoc ] using node_derives_right hnc h₄ );
    · simp_all +decide [ mc_node ]

/-! ## Ogden's lemma for CNF grammars -/

/-
PROBLEM
Ogden's lemma for CNF grammars. The pumping constant is `2 ^ g.generators.card`.

PROVIDED SOLUTION
1. Since hwg : w ∈ g.language, get a parse tree p with p.yield = w using Derives.yield (from hwg which gives g.Derives [nonterminal g.initial] (w.map terminal)).
2. Since countMarkedIn P 0 w.length ≥ 2^generators.card, we have p.mc P 0 ≥ 2^generators.card (since mc = countMarkedIn by definition, and p.yield = w).
3. From mc_implies_markedHeight, we get generators.card ≤ p.markedHeight P 0.
4. Use ogdens_restrict_mh with k = generators.card to find a subtree q with markedHeight = generators.card and mc > 0 and mc ≤ 2^generators.card (from mc_le_pow_markedHeight).
5. Apply ogdens_marked_path_decomp to q with s = ∅. Since generators.card ≤ q.markedHeight + 0 = generators.card, the precondition holds.
6. Since s = ∅, the Right case is impossible (no n' ∈ ∅).
7. So we get the Left case: decomposition of q.yield into u' v x y z' with the required properties.
8. Since p.yield = u₀ ++ q.yield ++ z₀, we have w = u₀ ++ (u' ++ v ++ x ++ y ++ z') ++ z₀ = (u₀ ++ u') ++ v ++ x ++ y ++ (z' ++ z₀).
9. Set u = u₀ ++ u', z = z' ++ z₀. The marked position properties transfer (adjusting offsets).
10. For the pumping: the derivation from q's root gives pumped words, and the outer derivation (from g.initial to u₀ ++ [q's root] ++ z₀) wraps them.
11. The pumped word is in g.language since we derive from g.initial.
-/
lemma ogdens_cnf {w : List T} (hwg : w ∈ g.language) (P : ℕ → Prop) [DecidablePred P]
    (hw : countMarkedIn P 0 w.length ≥ 2 ^ g.generators.card) :
    ∃ u v x y z : List T,
      w = u ++ v ++ x ++ y ++ z ∧
      0 < countMarkedIn P u.length v.length +
          countMarkedIn P (u.length + v.length + x.length) y.length ∧
      countMarkedIn P u.length (v.length + x.length + y.length) ≤
          2 ^ g.generators.card ∧
      ∀ i : ℕ, u ++ v ^+^ i ++ x ++ y ^+^ i ++ z ∈ g.language := by
  by_cases h_empty : ∃ p : ChomskyNormalFormGrammar.parseTree g.initial, p.yield = w ∧ p.markedHeight P 0 < g.generators.card;
  · obtain ⟨ p, rfl, hp ⟩ := h_empty;
    exact absurd hw ( not_le_of_gt ( lt_of_le_of_lt ( mc_le_pow_markedHeight P 0 p ) ( pow_lt_pow_right₀ ( by decide ) hp ) ) );
  · -- Apply the Ogden's lemma to the parse tree p.
    obtain ⟨p, hp⟩ : ∃ p : ChomskyNormalFormGrammar.parseTree g.initial, p.yield = w ∧ p.markedHeight P 0 ≥ g.generators.card := by
      obtain ⟨p, hp⟩ : ∃ p : ChomskyNormalFormGrammar.parseTree g.initial, p.yield = w := by
        -- Apply the lemma that states if there's a derivation from the initial nonterminal to the terminal symbols of w, then there exists a parse tree p with yield w.
        apply ChomskyNormalFormGrammar.Derives.yield; assumption;
      exact ⟨ p, hp, le_of_not_gt fun h => h_empty ⟨ p, hp, h ⟩ ⟩;
    -- Apply Ogden's lemma to find a marked path in the parse tree.
    obtain ⟨n', q, u₀, z₀, hq⟩ : ∃ n' : g.NT, ∃ q : parseTree n', ∃ u₀ z₀ : List T,
      p.yield = u₀ ++ q.yield ++ z₀ ∧
      q.markedHeight P (0 + u₀.length) = g.generators.card ∧
      0 < q.mc P (0 + u₀.length) ∧
      g.Derives [Symbol.nonterminal g.initial]
        (u₀.map Symbol.terminal ++ [Symbol.nonterminal n'] ++ z₀.map Symbol.terminal) := by
          apply ogdens_restrict_mh p P 0 g.generators.card hp.right (by
          have h_mc_pos : p.mc P 0 ≥ 2 ^ g.generators.card := by
            unfold mc; aesop;
          generalize_proofs at *; (
          exact lt_of_lt_of_le ( by positivity ) h_mc_pos));
    -- Apply Ogden's lemma to find a marked path in the parse tree q.
    obtain ⟨u', v, x, y, z', hq'⟩ : ∃ u' v x y z' : List T,
      q.yield = u' ++ v ++ x ++ y ++ z' ∧
      0 < countMarkedIn P (u₀.length + u'.length) v.length +
          countMarkedIn P (u₀.length + u'.length + v.length + x.length) y.length ∧
      countMarkedIn P (u₀.length + u'.length) (v.length + x.length + y.length) ≤
          2 ^ g.generators.card ∧
      ∀ i : ℕ, g.Derives [Symbol.nonterminal n']
        ((u' ++ v ^+^ i ++ x ++ y ^+^ i ++ z').map Symbol.terminal) := by
          have := ogdens_marked_path_decomp q P (u₀.length) ∅; simp_all +decide ;
          apply this;
          exact le_trans ( mc_le_pow_markedHeight P u₀.length q ) ( by simp +decide [ hq.2.1 ] );
    refine' ⟨ u₀ ++ u', v, x, y, z' ++ z₀, _, _, _, _ ⟩ <;> simp_all +decide [ List.append_assoc ];
    intro i
    have h_deriv : g.Derives [Symbol.nonterminal g.initial] (u₀.map Symbol.terminal ++ [Symbol.nonterminal n'] ++ z₀.map Symbol.terminal) := by
      convert hq.2.2.2 using 1 ; simp +decide [ List.append_assoc ]
    have h_deriv' : g.Derives [Symbol.nonterminal n'] ((u' ++ v ^+^ i ++ x ++ y ^+^ i ++ z').map Symbol.terminal) := by
      grind
    exact (by
    convert h_deriv.trans _ using 1
    generalize_proofs at *; (
    grind +suggestions))

end parseTree
end ChomskyNormalFormGrammar

/-! ## Ogden's lemma for general context-free languages -/

/-- Ogden's lemma for context-free languages (Mathlib formulation). -/
theorem Language.IsContextFree.ogdens_lemma {L : Language T} (hL : L.IsContextFree) :
    ∃ p : ℕ, ∀ (w : List T), w ∈ L →
      ∀ (P : ℕ → Prop) [DecidablePred P],
        p ≤ countMarkedIn P 0 w.length →
        ∃ u v x y z : List T,
          w = u ++ v ++ x ++ y ++ z ∧
          0 < countMarkedIn P u.length v.length +
              countMarkedIn P (u.length + v.length + x.length) y.length ∧
          countMarkedIn P u.length (v.length + x.length + y.length) ≤ p ∧
          ∀ i : ℕ, u ++ v ^+^ i ++ x ++ y ^+^ i ++ z ∈ L := by
  obtain ⟨g, rfl⟩ := hL
  classical
  use 2 ^ g.toCNF.generators.card
  intro w hwg P _ hw2
  by_cases hw : w = []
  · simp [hw] at hw2
  · obtain ⟨u, v, x, y, z, hw, hvy, hvxy, hL⟩ :=
      ChomskyNormalFormGrammar.parseTree.ogdens_cnf
        (g.toCNF_correct ▸ ⟨hwg, hw⟩) P hw2
    exact ⟨u, v, x, y, z, hw, hvy, hvxy, fun i => Set.diff_subset (g.toCNF_correct ▸ hL i)⟩

/-- Ogden's lemma for context-free languages (project formulation). -/
theorem CF_ogdens_lemma {L : Language T} (cf : is_CF L) :
    ∃ p : ℕ, ∀ (w : List T), w ∈ L →
      ∀ (P : ℕ → Prop) [DecidablePred P],
        p ≤ countMarkedIn P 0 w.length →
        ∃ u v x y z : List T,
          w = u ++ v ++ x ++ y ++ z ∧
          0 < countMarkedIn P u.length v.length +
              countMarkedIn P (u.length + v.length + x.length) y.length ∧
          countMarkedIn P u.length (v.length + x.length + y.length) ≤ p ∧
          ∀ i : ℕ, u ++ v ^+^ i ++ x ++ y ^+^ i ++ z ∈ L := by
  exact Language.IsContextFree.ogdens_lemma (is_CF_iff_isContextFree.mp cf)


/-! ## Counting in repeated lists -/

/-
PROBLEM
Count of symbol s in nTimes l n equals n * count in l.

PROVIDED SOLUTION
Induction on n. Base case: nTimes l 0 = [] has count 0. Inductive case: nTimes l (n+1) = l ++ nTimes l n, use count_append and inductive hypothesis.
-/
lemma count_nTimes {α : Type*} [DecidableEq α] (l : List α) (n : ℕ) (s : α) :
    List.count s (l ^+^ n) = n * List.count s l := by
  induction' n with n ih;
  · simp +decide [ nTimes ];
  · simp_all +decide [ add_mul, nTimes_succ_l ];
    ring

/-
PROBLEM
The pumped word's count of symbol s.

PROVIDED SOLUTION
Unfold all the appends and use count_append and count_nTimes. Just simp with count_append and count_nTimes, then ring.
-/
lemma pumped_count {α : Type*} [DecidableEq α] (u v x y z : List α) (s : α) (i : ℕ) :
    List.count s (u ++ v ^+^ i ++ x ++ y ^+^ i ++ z) =
      (List.count s u + List.count s x + List.count s z) + i * (List.count s v + List.count s y) := by
  simp +arith +decide [ count_nTimes, List.count_append ] ; ring;

/-! ## Marked position counting -/

/-
PROBLEM
countMarkedIn for the range [0, a+b+c) with P(k) = (a ≤ k < a+b) equals b.

PROVIDED SOLUTION
countMarkedIn (fun k => a ≤ k ∧ k < a + b) 0 (a + b + c) counts positions k in [0, a+b+c) with a ≤ k < a+b. These are exactly {a, a+1, ..., a+b-1}, which has cardinality b. Unfold countMarkedIn and show the filter gives {0, 1, ..., b-1} mapped to {a, a+1, ..., a+b-1}, or directly compute.
-/
lemma countMarkedIn_middle_range (a b c : ℕ) :
    countMarkedIn (fun k => a ≤ k ∧ k < a + b) 0 (a + b + c) = b := by
  unfold countMarkedIn; simp +decide [ Finset.sum_filter ] ; ring; (
  -- The set {i ∈ Finset.range (a + b + c) | a ≤ i ∧ i < a + b} is exactly the set {a, a+1, ..., a+b-1}.
  have h_set_eq : {i ∈ Finset.range (a + b + c) | a ≤ i ∧ i < a + b} = Finset.Ico a (a + b) := by
    ext; simp [Finset.mem_Ico, Finset.mem_range];
    exact fun _ _ => by linarith;
  rw [h_set_eq]
  simp +decide [Finset.card_range]);

/-! ## Structural lemmas about sorted lists over Fin 3 -/

/-
PROBLEM
A list of the form 0^a ++ 1^b ++ 2^c is sorted (Chain' (· ≤ ·)).

PROVIDED SOLUTION
The list 0^a ++ 1^b ++ 2^c is non-decreasing because 0 ≤ 0 within replicate 0s, 0 ≤ 1 at the boundary, 1 ≤ 1 within 1s, 1 ≤ 2 at the boundary, 2 ≤ 2 within 2s. Use Chain'_append and Chain'_replicate lemmas from Mathlib.
-/
lemma chain'_replicate_abc (a b c : ℕ) :
    (List.replicate a (0 : Fin 3) ++ List.replicate b 1 ++ List.replicate c 2).Chain' (· ≤ ·) := by
  induction' b with b hb generalizing a c <;> simp_all +arith +decide [ List.replicate ];
  · -- The list is non-decreasing because 0 ≤ 0 within the replicate 0s and 0 ≤ 2 at the boundary.
    apply List.isChain_append.mpr;
    grind;
  · rcases a with ( _ | a ) <;> simp_all +arith +decide [ List.replicate ];
    · -- The list is 1 followed by b ones and then c twos. The first element is 1, and the next elements are all 1s. So, 1 ≤ 1, which is true. Then, the rest of the elements are all 1s, which are equal to each other. So, the chain condition holds.
      simp [Chain'];
      induction' b with b hb generalizing c <;> simp_all +arith +decide [ List.replicate ];
      · induction c <;> simp_all +arith +decide [ List.isChain_iff_get ];
        rintro ⟨ _ | i, hi ⟩ <;> simp +arith +decide [ * ];
      · specialize hb 0 c ; aesop;
    · specialize hb ( a + 1 ) c ; simp_all +arith +decide [ List.replicate ];
      cases a <;> cases b <;> cases c <;> simp_all +arith +decide [ List.replicate ];
      all_goals simp_all +arith +decide [ Chain', List.replicate ];
      · induction ‹ℕ› <;> simp_all +arith +decide [ List.replicate ];
      · grind +ring;
      · grind +splitImp;
      · grind

/-
PROBLEM
Chain' is preserved by dropping elements from the front.

PROVIDED SOLUTION
Induction on n or use the fact that drop produces a suffix, and Chain' is preserved by taking suffixes. In Mathlib, List.Chain'.drop or similar should exist.
-/
lemma chain'_drop {α : Type*} {r : α → α → Prop} {l : List α} (h : l.Chain' r) (n : ℕ) :
    (l.drop n).Chain' r := by
  simp_all +decide [ Chain' ];
  exact h.drop _

/-
PROBLEM
Chain' is preserved by taking elements from the front.

PROVIDED SOLUTION
Use the fact that take produces a prefix, and Chain' is preserved by taking prefixes. Induction on n and l.
-/
lemma chain'_take {α : Type*} {r : α → α → Prop} {l : List α} (h : l.Chain' r) (n : ℕ) :
    (l.take n).Chain' r := by
  -- Apply the lemma that states the take of a chain is a chain.
  apply List.IsChain.take; assumption

/-- A contiguous substring (slice) of a Chain' list is Chain'. -/
lemma chain'_slice {α : Type*} {r : α → α → Prop} {l : List α} (h : l.Chain' r) (s n : ℕ) :
    ((l.drop s).take n).Chain' r :=
  chain'_take (chain'_drop h s) n

/-
PROBLEM
If u ++ v ++ w is Chain', then v is Chain'.

PROVIDED SOLUTION
Chain' r (u ++ v ++ w) implies Chain' r (u ++ v) (by Chain' of append), then Chain' r v (by suffix of Chain'). Use chain'_drop and chain'_take with appropriate indices, or use List.Chain'.append and its converses.
-/
lemma chain'_middle {α : Type*} {r : α → α → Prop} {u v w : List α}
    (h : (u ++ v ++ w).Chain' r) : v.Chain' r := by
  convert chain'_take ( chain'_drop h ( List.length u ) ) ( List.length v ) using 1;
  simp +decide [ List.drop_append, List.take_append ]

/-
PROBLEM
If a sorted list over Fin 3 has ≥ 2 distinct elements, then repeating it (n ≥ 2)
    gives a non-sorted list.

PROVIDED SOLUTION
Since l is sorted (Chain' (· ≤ ·)) with two distinct elements a ≠ b where both a,b ∈ l, we have l.head ≤ l.getLast and l.head ≠ l.getLast (otherwise all elements equal). So l.getLast > l.head (strict inequality in Fin 3). For n ≥ 2, l^+^n = l ++ l ++ ..., and l ++ l has the last element of first l (= l.getLast) followed by first element of second l (= l.head). Since l.getLast > l.head, this is a descent, so l ++ l is not Chain' (· ≤ ·), hence l^+^n is not Chain' (· ≤ ·).
-/
lemma nTimes_not_chain'_of_distinct {l : List (Fin 3)} {n : ℕ}
    (hl : l.Chain' (· ≤ ·))
    (h_distinct : ∃ a b : Fin 3, a ≠ b ∧ a ∈ l ∧ b ∈ l)
    (hn : 2 ≤ n) :
    ¬ (l ^+^ n).Chain' (· ≤ ·) := by
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ List.replicate ] ;
  rcases l with ( _ | ⟨ a, _ | ⟨ b, l ⟩ ⟩ ) <;> simp_all +decide [ nTimes ];
  fin_cases a <;> fin_cases b <;> simp_all +decide [ Chain' ];
  grind;
  · grind;
  · grind +splitIndPred;
  · grind;
  · grind;
  · grind +splitImp

/-! ## Pigeonhole for three symbols -/

/-
PROBLEM
If v ++ y contains all three symbols {0,1,2} of Fin 3, then at least one of v, y
    contains two distinct elements.

PROVIDED SOLUTION
v++y has positive counts of 0, 1, and 2. If both v and y each contain at most 1 distinct element, then the union of their element sets has at most 2 elements. But the union must contain {0,1,2} (3 elements). Contradiction. So at least one of v, y has ≥ 2 distinct elements. Use List.count_pos_iff_mem to convert counts to membership.
-/
lemma pigeonhole_three_symbols_fin3 {v y : List (Fin 3)}
    (h0 : 0 < List.count 0 v + List.count 0 y)
    (h1 : 0 < List.count 1 v + List.count 1 y)
    (h2 : 0 < List.count 2 v + List.count 2 y) :
    (∃ a b : Fin 3, a ≠ b ∧ a ∈ v ∧ b ∈ v) ∨ (∃ a b : Fin 3, a ≠ b ∧ a ∈ y ∧ b ∈ y) := by
  simp_all +decide [ Fin.forall_fin_succ, List.count ];
  grind +ring
