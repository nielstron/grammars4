import Mathlib
import Grammars.Automata.LinearBounded.Basics.NLBA
import Grammars.Automata.LinearBounded.Equivalence.NLBAToCSG
import Grammars.Classes.ContextSensitive.Basics.Definition
import Grammars.Classes.ContextSensitive.Basics.Toolbox

/-!
# Myhill Forward Direction: NLBA Acceptance → Grammar Derivation

Helper lemmas for proving the forward direction of Myhill's construction:
if the NLBA accepts a word `w`, then `w` is derivable in the Myhill grammar.

The proof is organized into three phases:
1. **Initialization**: Derive the initial configuration from the start symbol
2. **Simulation**: Each NLBA step corresponds to a grammar derivation step
3. **Cleanup**: Convert the final accepting configuration to terminal symbols
-/

open List Relation Classical

noncomputable section

namespace MyhillConstruction

variable {T Γ Λ : Type}
variable [Fintype T] [Fintype Γ] [Fintype Λ]
variable [DecidableEq T] [DecidableEq Γ] [DecidableEq Λ]
variable (M : NLBA.Machine Γ Λ) (embed : T ↪ Γ)

/-! ### Extended Configuration -/

/-- Extended configuration: NLBA state + tape + original input at each cell. -/
structure ExtCfg (T Γ Λ : Type) (n : ℕ) where
  /-- Current state of the NLBA -/
  state : Λ
  /-- Head position -/
  head : Fin (n + 1)
  /-- Current tape contents -/
  tape : Fin (n + 1) → Γ
  /-- Original input symbols (invariant during computation) -/
  input : Fin (n + 1) → T

/-- Encode an extended configuration as a sentential form in the Myhill grammar. -/
def encodeExtCfg {n : ℕ} (ecfg : ExtCfg T Γ Λ n) :
    List (symbol T (MyhillNT T Γ Λ)) :=
  (List.finRange (n + 1)).map fun i =>
    let lb := decide (i.val = 0)
    let rb := decide (i.val = n)
    let q := if i = ecfg.head then some ecfg.state else none
    symbol.nonterminal (MyhillNT.cell lb rb q (ecfg.tape i) (ecfg.input i))

/-- The initial extended configuration for input word w. -/
def initExtCfg (w : List T) (hw : w ≠ []) :
    ExtCfg T Γ Λ (w.length - 1) where
  state := M.initial
  head := ⟨0, by have := List.length_pos_of_ne_nil hw; omega⟩
  tape := fun i => embed (w.get ⟨i.val, by
    have := i.isLt; have := List.length_pos_of_ne_nil hw; omega⟩)
  input := fun i => w.get ⟨i.val, by
    have := i.isLt; have := List.length_pos_of_ne_nil hw; omega⟩

/-! ### Phase 1: Initialization -/

/-
PROBLEM
Single-cell initialization: derive from start to a single cell.

PROVIDED SOLUTION
Use the single_cell_init_rule_mem to get the rule, then exhibit it as a CS_transforms witness with u=[] and v=[]. The rule has context_left=[], input_nonterminal=start, context_right=[], output_string=[cellSym ...]. So w₁ = [] ++ [] ++ [nt start] ++ [] ++ [] = [nt start] and w₂ = [] ++ [] ++ [cellSym ...] ++ [] ++ [] = [cellSym ...]. Use exact ⟨_, [], [], single_cell_init_rule_mem M embed t, by simp, by simp⟩.
-/
lemma init_single_cell_transforms (t : T) :
    CS_transforms (myhillGrammar M embed)
      [symbol.nonterminal MyhillNT.start]
      [cellSym true true (some M.initial) (embed t) t] := by
  use ⟨[], MyhillNT.start, [], [cellSym true true (some M.initial) (embed t) t]⟩;
  exact ⟨ [ ], [ ], single_cell_init_rule_mem M embed t, rfl, rfl ⟩

/-
PROBLEM
First cell of multi-cell initialization.

PROVIDED SOLUTION
Use first_cell_init_rule_mem with u=[] and v=[]. exact ⟨_, [], [], first_cell_init_rule_mem M embed t, by simp, by simp⟩.
-/
lemma init_first_cell_transforms (t : T) :
    CS_transforms (myhillGrammar M embed)
      [symbol.nonterminal MyhillNT.start]
      [cellSym true false (some M.initial) (embed t) t,
       symbol.nonterminal .startAux] := by
  obtain ⟨q, hq⟩ : ∃ q : csrule T (MyhillNT T Γ Λ), q ∈ (myhillGrammar M embed).rules ∧ q.context_left = [] ∧ q.input_nonterminal = MyhillNT.start ∧ q.context_right = [] ∧ q.output_string = [cellSym true false (some M.initial) (embed t) t, symbol.nonterminal MyhillNT.startAux] := by
    exact ⟨ _, first_cell_init_rule_mem M embed t, rfl, rfl, rfl, rfl ⟩;
  exact ⟨ q, [ ], [ ], hq.1, by aesop ⟩

/-
PROBLEM
Middle cell: expand startAux to a middle cell + startAux, in context u.

PROVIDED SOLUTION
Use middle_cell_init_rule_mem with u=u and v=[]. The CS_transforms definition requires:
w₁ = u' ++ r.context_left ++ [nt r.input_nonterminal] ++ r.context_right ++ v'
w₂ = u' ++ r.context_left ++ r.output_string ++ r.context_right ++ v'

With r = the middle cell rule (context_left=[], input_nonterminal=startAux, context_right=[], output_string=[cellSym ..., nt startAux]), u'=u, v'=[]:
w₁ = u ++ [] ++ [nt startAux] ++ [] ++ [] = u ++ [nt startAux]
w₂ = u ++ [] ++ [cellSym ..., nt startAux] ++ [] ++ [] = u ++ [cellSym ..., nt startAux]

exact ⟨_, u, [], middle_cell_init_rule_mem M embed t, by simp, by simp⟩
-/
lemma init_middle_cell_transforms (u : List (symbol T (MyhillNT T Γ Λ))) (t : T) :
    CS_transforms (myhillGrammar M embed)
      (u ++ [symbol.nonterminal MyhillNT.startAux])
      (u ++ [cellSym false false none (embed t) t,
             symbol.nonterminal .startAux]) := by
  refine' ⟨ _, u, [], _, _, _ ⟩ <;> norm_num;
  exact ⟨ [ ], MyhillNT.startAux, [ ], [ cellSym false false none ( embed t ) t, symbol.nonterminal MyhillNT.startAux ] ⟩;
  · exact MyhillConstruction.middle_cell_init_rule_mem M embed t;
  · rfl;
  · rfl

/-
PROBLEM
Last cell: expand startAux to the last cell, in context u.

PROVIDED SOLUTION
Use the same pattern as init_middle_cell_transforms but with the last_cell_init_rule_mem rule. The rule has context_left=[], input_nonterminal=startAux, context_right=[], output_string=[cellSym false true none (embed t) t].

refine ⟨⟨[], MyhillNT.startAux, [], [cellSym false true none (embed t) t]⟩, u, [], last_cell_init_rule_mem M embed t, ?_, ?_⟩
Then both goals should be about list equality, provable by simp or rfl.
-/
lemma init_last_cell_transforms (u : List (symbol T (MyhillNT T Γ Λ))) (t : T) :
    CS_transforms (myhillGrammar M embed)
      (u ++ [symbol.nonterminal MyhillNT.startAux])
      (u ++ [cellSym false true none (embed t) t]) := by
  -- Apply the rule from last_cell_init_rule_mem to replace the startAux symbol with the cell symbol.
  have h_rule : ∃ r : csrule T (MyhillNT T Γ Λ), r ∈ myhillAllRules M embed ∧ r.context_left = [] ∧ r.input_nonterminal = MyhillNT.startAux ∧ r.context_right = [] ∧ r.output_string = [cellSym false true none (embed t) t] := by
    exact ⟨ _, last_cell_init_rule_mem M embed t, rfl, rfl, rfl, rfl ⟩;
  obtain ⟨ r, hr₁, hr₂, hr₃, hr₄, hr₅ ⟩ := h_rule; use r; aesop;

/-
PROBLEM
Helper: derive from startAux to a sequence of cells for the tail of the word.
Given a prefix u already derived, derive the cells for the remaining elements.

PROVIDED SOLUTION
Prove by induction on tail.

Base case: tail = [t] (htail says tail ≠ []).
  We need: CS_derives ... (u ++ [nt startAux]) (u ++ [cellSym false true none (embed t) t])
  Note: mapIdx of [t] with index 0 gives [cellSym false (decide (0 = 0)) none (embed t) t] = [cellSym false true none (embed t) t]
  since tail.length - 1 = 0.
  Apply CS_deri_of_tran with init_last_cell_transforms.

Inductive case: tail = t :: t' :: rest.
  We need: CS_derives ... (u ++ [nt startAux]) (u ++ mapIdx ...)
  Step 1: Apply init_middle_cell_transforms to get:
    CS_derives (u ++ [nt startAux]) (u ++ [cellSym false false none (embed t) t, nt startAux])
  Note: mapIdx of (t :: t' :: rest) gives cell(false, decide(0=len-1), none, embed t, t) :: mapIdx(1, t'::rest)
  Since len ≥ 2, decide(0=len-1) = false, so the first element is cellSym false false none (embed t) t.
  Step 2: Apply the induction hypothesis with u' = u ++ [cellSym false false none (embed t) t] and tail' = t' :: rest.
  Compose with CS_deri_of_deri_deri.

  The tricky part is showing that the mapIdx functions match up. We need:
  u ++ mapIdx(0, t :: t' :: rest) = u ++ [cellSym false false none (embed t) t] ++ mapIdx(0, t' :: rest)
  where the first mapIdx uses (t::t'::rest).length-1 and the second uses (t'::rest).length-1.

  Wait, this doesn't quite work because the boundary flag `rb` depends on the position relative to the TOTAL tail length. When we recurse, the sub-tail has a different length, so the boundary flags would be wrong.

Actually, we need to be more careful. Let me re-state the lemma to handle this.

The mapIdx for tail = [t₁, t₂, ..., tₖ] produces:
  [cellSym false (k=1?) none (embed t₁) t₁, cellSym false (k=2?) none (embed t₂) t₂, ..., cellSym false true none (embed tₖ) tₖ]

When we recurse on [t₂, ..., tₖ], the mapIdx produces:
  [cellSym false (k-1=1?) none (embed t₂) t₂, ..., cellSym false true none (embed tₖ) tₖ]

The boundary flag for the last element is always `true` (decide (i = tail.length - 1) where i is the last index).
For non-last elements, it's `false`.

Since mapIdx gives each element its 0-based index within the sub-list, and the boundary condition is `decide (i = tail.length - 1)`, the recursion works correctly:
- In the full tail [t₁, ..., tₖ]: last element has index k-1, decide(k-1 = k-1) = true. Other elements have decide(i = k-1) = false.
- In the sub-tail [t₂, ..., tₖ]: last element has index k-2, decide(k-2 = k-2) = true. Other elements have decide(i = k-2) = false.

So the recursion does work! The first element of the full mapIdx has decide(0 = k-1). For k ≥ 2, this is false, matching cellSym false false none ....

So the proof is:
1. Case tail = [t]: apply init_last_cell_transforms, then show mapIdx matches.
2. Case tail = t :: t' :: rest: apply init_middle_cell_transforms, then use IH on t' :: rest with prefix u ++ [cellSym false false none (embed t) t], then show mapIdx matches via List.mapIdx_cons or similar.
-/
lemma init_tail_derives (u : List (symbol T (MyhillNT T Γ Λ)))
    (tail : List T) (htail : tail ≠ []) :
    CS_derives (myhillGrammar M embed)
      (u ++ [symbol.nonterminal MyhillNT.startAux])
      (u ++ tail.mapIdx (fun i t =>
        cellSym false (decide (i = tail.length - 1)) none (embed t) t)) := by
  -- We'll use induction on the length of the tail.
  induction' tail with t tail ih generalizing u;
  · contradiction;
  · rcases tail <;> simp_all +decide [ List.mapIdx_cons ];
    · exact .single (init_last_cell_transforms M embed u t);
    · have := ih ( u ++ [ cellSym false false none ( embed t ) t ] );
      convert CS_deri_of_deri_deri _ _ using 1;
      exact u ++ [ cellSym false false none ( embed t ) t ] ++ [ symbol.nonterminal MyhillNT.startAux ];
      · exact Relation.ReflTransGen.single ( by simpa using init_middle_cell_transforms M embed u t );
      · simpa [ List.append_assoc ] using this

/-
PROBLEM
The start symbol derives the encoding of the initial configuration.

PROVIDED SOLUTION
Case split on w.

Case w = [t] (single element):
  n = 0. encodeExtCfg (initExtCfg M embed [t] hw) = [cellSym true true (some M.initial) (embed t) t].
  (Because finRange 1 = [⟨0,_⟩], lb = decide(0=0) = true, rb = decide(0=0) = true, head=0 so q = some M.initial.)
  Apply CS_deri_of_tran with init_single_cell_transforms.
  Need to show encodeExtCfg (initExtCfg M embed [t] hw) = [cellSym true true (some M.initial) (embed t) t].

Case w = t :: t' :: rest (multiple elements):
  n = w.length - 1 ≥ 1.
  Step 1: Apply init_first_cell_transforms for t:
    [nt start] derives [cellSym true false (some M.initial) (embed t) t, nt startAux]
  Step 2: Apply init_tail_derives with u = [cellSym true false (some M.initial) (embed t) t] and tail = t' :: rest:
    [cellSym(...), nt startAux] derives [cellSym(...)] ++ mapIdx(t'::rest)

  Then show that the result equals encodeExtCfg (initExtCfg M embed w hw).

  encodeExtCfg (initExtCfg M embed (t::t'::rest) hw) maps finRange (n+1) where n = length - 1 = (t'::rest).length.
  The first element (i=0): lb=true, rb=false (since n≥1), q=some M.initial, tape=embed t, input=t.
  This is cellSym true false (some M.initial) (embed t) t.

  The remaining elements (i=1,...,n): lb=false, rb=decide(i=n), q=none (since head=0 and i≥1), tape=embed(w[i]), input=w[i].
  These should match mapIdx of (t'::rest) with appropriate boundary conditions.

Use CS_deri_of_deri_deri to compose steps 1 and 2.
Use CS_deri_of_tran to convert single transforms to derives.
-/
theorem init_derives (w : List T) (hw : w ≠ []) :
    CS_derives (myhillGrammar M embed)
      [symbol.nonterminal MyhillNT.start]
      (encodeExtCfg (initExtCfg M embed w hw)) := by
  rcases w with ( _ | ⟨ t, _ | ⟨ t', w ⟩ ⟩ ) <;> simp_all +decide [ CS_derives ];
  · contradiction;
  · convert CS_deri_of_tran ( init_single_cell_transforms M embed t ) using 1;
  · have := init_first_cell_transforms M embed t; ( have := init_tail_derives M embed [cellSym true false (some M.initial) (embed t) t] (t' :: w) (by simp [hw]) ; );
    convert this.head _ using 1;
    · unfold encodeExtCfg initExtCfg; simp +decide [ List.finRange_succ ] ;
      refine' ⟨ ⟨ fun h => by simp [ h ], fun h => by simpa using h.symm ⟩, _ ⟩;
      refine' List.ext_get _ _ <;> simp +decide [ Function.comp ];
    · assumption

/-! ### Context lemmas for CS derivations -/

/-
PROBLEM
CS transforms preserved under left-append.

PROVIDED SOLUTION
From h : CS_transforms, extract ⟨r, u, v, hr, hw₁, hw₂⟩. Then construct the transform with u' = pre ++ u and same v, r:
exact ⟨r, pre ++ u, v, hr, by rw [hw₁]; simp [List.append_assoc], by rw [hw₂]; simp [List.append_assoc]⟩
-/
lemma CS_transforms_append_left (pre : List (symbol T (MyhillNT T Γ Λ)))
    {w₁ w₂ : List (symbol T (MyhillNT T Γ Λ))}
    (h : CS_transforms (myhillGrammar M embed) w₁ w₂) :
    CS_transforms (myhillGrammar M embed) (pre ++ w₁) (pre ++ w₂) := by
  obtain ⟨ r, u, v, hr, hw₁, hw₂ ⟩ := h;
  apply Exists.intro r;
  grind

/-
PROBLEM
CS derives preserved under left-append.

PROVIDED SOLUTION
Induction on h : CS_derives. Base: refl. Step: use CS_deri_of_deri_deri ih (CS_deri_of_tran (CS_transforms_append_left M embed pre step)).
-/
lemma CS_derives_append_left (pre : List (symbol T (MyhillNT T Γ Λ)))
    {w₁ w₂ : List (symbol T (MyhillNT T Γ Λ))}
    (h : CS_derives (myhillGrammar M embed) w₁ w₂) :
    CS_derives (myhillGrammar M embed) (pre ++ w₁) (pre ++ w₂) := by
  induction' h with w₁' w₂' h' h'' ih₁ ih₂;
  · constructor;
  · exact ih₁.tail ( by simpa using CS_transforms_append_left M embed pre h'' )

/-
PROBLEM
CS derives preserved under right-append.

PROVIDED SOLUTION
Induction on h : CS_derives. Base: refl. Step: extract ⟨r, u, v, hr, hw₁, hw₂⟩ from the single step. Construct the new step with u' = u, v' = v ++ suffix, same r. Use CS_deri_of_deri_deri ih (CS_deri_of_tran ⟨r, u, v ++ suffix, hr, by simp [hw₁, List.append_assoc], by simp [hw₂, List.append_assoc]⟩).
-/
lemma CS_derives_append_right (suffix : List (symbol T (MyhillNT T Γ Λ)))
    {w₁ w₂ : List (symbol T (MyhillNT T Γ Λ))}
    (h : CS_derives (myhillGrammar M embed) w₁ w₂) :
    CS_derives (myhillGrammar M embed) (w₁ ++ suffix) (w₂ ++ suffix) := by
  revert w₁ w₂ h;
  intros w₁ w₂ h; induction' h with w₁ w₂ h ih <;> simp_all +decide [ CS_derives ] ;
  · rfl;
  · obtain ⟨ r, u, v, hr, hw₁, hw₂ ⟩ := ih;
    exact .trans ‹_› ( Relation.ReflTransGen.single <| by exact ⟨ _, _, _, hr, by aesop ⟩ )

/-- Propagate right: replace a none-cell immediately before a terminal. -/
lemma cleanup_right_prop_transforms
    (u : List (symbol T (MyhillNT T Γ Λ)))
    (v : List (symbol T (MyhillNT T Γ Λ)))
    (lb rb : Bool) (a : Γ) (t₁ t₂ : T) :
    CS_transforms (myhillGrammar M embed)
      (u ++ [symbol.nonterminal (MyhillNT.cell lb rb none a t₁),
             symbol.terminal t₂] ++ v)
      (u ++ [symbol.terminal t₁, symbol.terminal t₂] ++ v) := by
  use ⟨[], MyhillNT.cell lb rb none a t₁, [symbol.terminal t₂], [symbol.terminal t₁]⟩;
  exact ⟨ u, v, right_propagation_rule_mem M embed a t₁ t₂ lb rb, by simp +decide, by simp +decide ⟩

/-- Propagate left: replace a none-cell immediately after a terminal. -/
lemma cleanup_left_prop_transforms
    (u : List (symbol T (MyhillNT T Γ Λ)))
    (v : List (symbol T (MyhillNT T Γ Λ)))
    (lb rb : Bool) (a : Γ) (t₁ t₂ : T) :
    CS_transforms (myhillGrammar M embed)
      (u ++ [symbol.terminal t₁,
             symbol.nonterminal (MyhillNT.cell lb rb none a t₂)] ++ v)
      (u ++ [symbol.terminal t₁, symbol.terminal t₂] ++ v) := by
  apply Exists.intro (⟨[symbol.terminal t₁], MyhillNT.cell lb rb none a t₂, [], [symbol.terminal t₂]⟩ : csrule T (MyhillNT T Γ Λ));
  exact ⟨ u, v, left_propagation_rule_mem M embed t₁ a t₂ lb rb, by simp +decide, by simp +decide ⟩

/-! ### Propagation lemmas -/

/-
PROBLEM
Propagate rightward: convert cells to terminals left-to-right,
    given a terminal immediately to the left.

PROVIDED SOLUTION
Induction on cells, generalizing u and t_left.

Base (cells = []): Both sides are equal, use ReflTransGen.refl.

Step (cells = ⟨lb, rb, a, t⟩ :: rest):
Goal: CS_derives (u ++ [terminal t_left] ++ [cellSym lb rb none a t] ++ rest.map cellSym_func)
                  (u ++ [terminal t_left] ++ [terminal t] ++ rest.map terminal_func)

Step 1: Apply cleanup_left_prop_transforms M embed u (rest.map (fun ...)) lb rb a t_left t.
This is a single CS_transforms from:
  u ++ [terminal t_left, cellSym lb rb none a t] ++ rest.map cellSym_func
to:
  u ++ [terminal t_left, terminal t] ++ rest.map cellSym_func

Step 2: Apply IH (ih) with u' = u ++ [terminal t_left] and t_left' = t:
  (u ++ [terminal t_left]) ++ [terminal t] ++ rest.map cellSym_func
  →(CS) (u ++ [terminal t_left]) ++ [terminal t] ++ rest.map terminal_func

Compose with CS_deri_of_deri_deri.
Need to handle List.append_assoc to match the forms.
-/
lemma propagate_right_list (u : List (symbol T (MyhillNT T Γ Λ)))
    (t_left : T)
    (cells : List (Bool × Bool × Γ × T)) :
    CS_derives (myhillGrammar M embed)
      (u ++ [symbol.terminal t_left] ++
       cells.map (fun ⟨lb, rb, a, t⟩ => (cellSym lb rb none a t : symbol T (MyhillNT T Γ Λ))))
      (u ++ [symbol.terminal t_left] ++
       cells.map (fun ⟨_, _, _, t⟩ => (symbol.terminal t : symbol T (MyhillNT T Γ Λ)))) := by
  induction cells generalizing u t_left <;> simp_all +decide [ List.map ];
  · constructor;
  · rename_i k hk ih;
    obtain ⟨ cell₁, cell₂ ⟩ := k ; simp_all +decide [ List.map ] ;
    have h_step : CS_derives (myhillGrammar M embed) (u ++ [symbol.terminal t_left, cellSym cell₁ cell₂.1 none cell₂.2.1 cell₂.2.2] ++ map (fun x => cellSym x.1 x.2.1 none x.2.2.1 x.2.2.2) hk) (u ++ [symbol.terminal t_left, symbol.terminal cell₂.2.2] ++ map (fun x => cellSym x.1 x.2.1 none x.2.2.1 x.2.2.2) hk) := by
      have h_step : CS_transforms (myhillGrammar M embed) (u ++ [symbol.terminal t_left, cellSym cell₁ cell₂.1 none cell₂.2.1 cell₂.2.2] ++ map (fun x => cellSym x.1 x.2.1 none x.2.2.1 x.2.2.2) hk) (u ++ [symbol.terminal t_left, symbol.terminal cell₂.2.2] ++ map (fun x => cellSym x.1 x.2.1 none x.2.2.1 x.2.2.2) hk) := by
        exact cleanup_left_prop_transforms M embed u _ cell₁ cell₂.1 cell₂.2.1 t_left cell₂.2.2;
      exact .single h_step;
    convert h_step.trans _ using 1;
    · simp +decide [ List.append_assoc ];
    · convert ih ( u ++ [ symbol.terminal t_left ] ) cell₂.2.2 using 1 ; simp +decide [ List.append_assoc ];
      simp +decide [ List.append_assoc ]

/-
PROBLEM
Propagate leftward: convert cells to terminals right-to-left,
    given a terminal immediately to the right.

PROVIDED SOLUTION
Induction on cells, generalizing t_right and v.

Base (cells = []): Refl.

Step (cells = ⟨lb, rb, a, t⟩ :: rest):
The sentential form is:
  [cellSym lb rb none a t] ++ rest.map cellSym_func ++ [terminal t_right] ++ v

Strategy:
1. Apply IH on rest (with t_right, v unchanged) to clean up the tail:
   rest.map cellSym_func ++ [terminal t_right] ++ v → rest.map terminal_func ++ [terminal t_right] ++ v
2. Use CS_derives_append_left to prepend [cellSym lb rb none a t]:
   [cellSym] ++ rest.map cellSym ++ [terminal t_right] ++ v → [cellSym] ++ rest.map terminal ++ [terminal t_right] ++ v
3. Now the first cell (cellSym lb rb none a t) is followed by either:
   - If rest non-empty: terminal from rest_terminals (first element)
   - If rest empty: terminal t_right
   In either case, it's adjacent to a terminal.
4. Apply cleanup_right_prop_transforms to convert the first cell:
   [cellSym lb rb none a t, terminal t_next] ++ remaining → [terminal t, terminal t_next] ++ remaining

Compose steps 2-4 with CS_deri_of_deri_deri.

For step 2, use CS_derives_append_left M embed [cellSym lb rb none a t] (ih t_right v).

For step 4, case-split on rest:
- rest = []: form is [cellSym lb rb none a t, terminal t_right] ++ v. Apply right_prop.
- rest = ⟨lb', rb', a', t'⟩ :: rest': form is [cellSym lb rb none a t, terminal t'] ++ (...). Apply right_prop with u=[], t₁=t, t₂=t'.

Use cleanup_right_prop_transforms for the conversion.
-/
lemma propagate_left_list
    (cells : List (Bool × Bool × Γ × T))
    (t_right : T)
    (v : List (symbol T (MyhillNT T Γ Λ))) :
    CS_derives (myhillGrammar M embed)
      (cells.map (fun ⟨lb, rb, a, t⟩ => (cellSym lb rb none a t : symbol T (MyhillNT T Γ Λ))) ++
       [symbol.terminal t_right] ++ v)
      (cells.map (fun ⟨_, _, _, t⟩ => (symbol.terminal t : symbol T (MyhillNT T Γ Λ))) ++
       [symbol.terminal t_right] ++ v) := by
  induction' cells using List.reverseRecOn with cells ih generalizing t_right v;
  · constructor;
  · obtain ⟨ cell₁, cell₂ ⟩ := ih ; simp_all +decide [ List.map_append ];
    rename_i h;
    have h_propagate_left : CS_derives (myhillGrammar M embed) ((map (fun x => cellSym x.1 x.2.1 none x.2.2.1 x.2.2.2) cells) ++ [cellSym cell₁ cell₂.1 none cell₂.2.1 cell₂.2.2, symbol.terminal t_right] ++ v) ((map (fun x => cellSym x.1 x.2.1 none x.2.2.1 x.2.2.2) cells) ++ [symbol.terminal cell₂.2.2, symbol.terminal t_right] ++ v) := by
      have h_propagate_left : CS_transforms (myhillGrammar M embed) ((map (fun x => cellSym x.1 x.2.1 none x.2.2.1 x.2.2.2) cells) ++ [cellSym cell₁ cell₂.1 none cell₂.2.1 cell₂.2.2, symbol.terminal t_right] ++ v) ((map (fun x => cellSym x.1 x.2.1 none x.2.2.1 x.2.2.2) cells) ++ [symbol.terminal cell₂.2.2, symbol.terminal t_right] ++ v) := by
        exact cleanup_right_prop_transforms M embed _ v cell₁ cell₂.1 cell₂.2.1 cell₂.2.2 t_right;
      exact .single h_propagate_left;
    simp +zetaDelta at *;
    exact h_propagate_left.trans ( h _ _ )

/-! ### Phase 2: Simulation -/

/-- Helper: two encodeExtCfg lists that agree everywhere produce the same list. -/
lemma encodeExtCfg_ext {n : ℕ} (ecfg₁ ecfg₂ : ExtCfg T Γ Λ n)
    (h : ∀ i : Fin (n + 1),
      decide (i.val = 0) = decide (i.val = 0) ∧
      decide (i.val = n) = decide (i.val = n) ∧
      (if i = ecfg₁.head then some ecfg₁.state else none) =
        (if i = ecfg₂.head then some ecfg₂.state else none) ∧
      ecfg₁.tape i = ecfg₂.tape i ∧
      ecfg₁.input i = ecfg₂.input i) :
    encodeExtCfg ecfg₁ = encodeExtCfg ecfg₂ := by
  unfold encodeExtCfg
  congr 1
  ext i
  have := h i
  simp_all

/-- The take/drop parts of encodeExtCfg are determined by the cells at those positions. -/
lemma encodeExtCfg_take {n : ℕ} (ecfg : ExtCfg T Γ Λ n) (k : ℕ) :
    (encodeExtCfg ecfg).take k =
    ((List.finRange (n + 1)).map fun i =>
      let lb := decide (i.val = 0)
      let rb := decide (i.val = n)
      let q := if i = ecfg.head then some ecfg.state else none
      symbol.nonterminal (MyhillNT.cell lb rb q (ecfg.tape i) (ecfg.input i))).take k := by
  rfl

/-
PROBLEM
Simulation case: single-cell update (covers stay, right-boundary, left-boundary).
    When the head doesn't actually move, only the cell at head changes.

PROVIDED SOLUTION
The head doesn't move. Use finRange_map_split to decompose encodeExtCfg ecfg₁ at ecfg₁.head:
  encodeExtCfg ecfg₁ = take(head) ++ [cell(lb, rb, some state, tape[head], input[head])] ++ drop(head+1)

The rule replaces the single cell at head:
  [cell(lb, rb, some state, tape[head], input[head])] → [cell(lb, rb, some q', a', input[head])]

So CS_transforms with u = take(head), v = drop(head+1), rule = h_rule.

For the output side, show encodeExtCfg ecfg₂ = take(head) ++ [cell(lb, rb, some q', a', input[head])] ++ drop(head+1).

Since ecfg₂.head = ecfg₁.head, ecfg₂.state = q', ecfg₂.tape = update tape head a', ecfg₂.input = ecfg₁.input:
- take(head) of ecfg₂ = take(head) of ecfg₁ (at positions i < head: tape[i] unchanged since i ≠ head, head marker absent since i ≠ head = ecfg₂.head, input unchanged)
- Cell at head in ecfg₂: lb, rb same, q = some q' (since head = ecfg₂.head), tape = a' (update_same), input[head] same
- drop(head+1) of ecfg₂ = drop(head+1) of ecfg₁ (at positions i > head: tape[i] unchanged, head marker absent)

Apply ReflTransGen.single with the CS_transforms witness.
-/
lemma sim_step_single_cell {n : ℕ}
    (ecfg₁ : ExtCfg T Γ Λ n)
    (q' : Λ) (a' : Γ)
    (h_head_same : ∀ ecfg₂ : ExtCfg T Γ Λ n,
      ecfg₂.head = ecfg₁.head → ecfg₂.state = q' →
      ecfg₂.tape = Function.update ecfg₁.tape ecfg₁.head a' →
      ecfg₂.input = ecfg₁.input → True)
    (h_rule : (⟨[], MyhillNT.cell (decide (ecfg₁.head.val = 0)) (decide (ecfg₁.head.val = n))
        (some ecfg₁.state) (ecfg₁.tape ecfg₁.head) (ecfg₁.input ecfg₁.head), [],
      [cellSym (decide (ecfg₁.head.val = 0)) (decide (ecfg₁.head.val = n))
        (some q') a' (ecfg₁.input ecfg₁.head)]⟩ :
      csrule T (MyhillNT T Γ Λ)) ∈ myhillAllRules M embed) :
    let ecfg₂ : ExtCfg T Γ Λ n := ⟨q', ecfg₁.head,
      Function.update ecfg₁.tape ecfg₁.head a', ecfg₁.input⟩
    CS_derives (myhillGrammar M embed)
      (encodeExtCfg ecfg₁)
      (encodeExtCfg ecfg₂) := by
  unfold encodeExtCfg
  generalize_proofs at *;
  apply_rules [ ReflTransGen.single ];
  use ⟨[], MyhillNT.cell (decide (ecfg₁.head.val = 0)) (decide (ecfg₁.head.val = n)) (some ecfg₁.state) (ecfg₁.tape ecfg₁.head) (ecfg₁.input ecfg₁.head), [], [cellSym (decide (ecfg₁.head.val = 0)) (decide (ecfg₁.head.val = n)) (some q') a' (ecfg₁.input ecfg₁.head)]⟩;
  refine' ⟨ List.take ecfg₁.head ( List.finRange ( n + 1 ) |> List.map fun i => symbol.nonterminal ( MyhillNT.cell ( decide ( i.val = 0 ) ) ( decide ( i.val = n ) ) ( if i = ecfg₁.head then some ecfg₁.state else none ) ( ecfg₁.tape i ) ( ecfg₁.input i ) ) ), List.drop ( ecfg₁.head + 1 ) ( List.finRange ( n + 1 ) |> List.map fun i => symbol.nonterminal ( MyhillNT.cell ( decide ( i.val = 0 ) ) ( decide ( i.val = n ) ) ( if i = ecfg₁.head then some ecfg₁.state else none ) ( ecfg₁.tape i ) ( ecfg₁.input i ) ) ), _, _ ⟩ <;> simp +decide [ * ];
  · aesop;
  · constructor <;> ext i <;> simp +decide [ List.getElem?_append, List.getElem?_take, List.getElem?_drop ];
    · grind;
    · grind

/-
PROBLEM
Split a mapped finRange list at two consecutive positions.

PROVIDED SOLUTION
Use finRange_map_split at position k to get:
  list = take(k) ++ [f k] ++ drop(k+1)

Then note that drop(k+1) starts with f(k+1) (since k+1 ≤ n, so k+1 < n+1, the list has at least k+2 elements). We can write:
  drop(k+1) = [f(k+1)] ++ drop(k+2)

This follows from List.drop_eq_getElem_cons or by showing drop(k+1) = getElem(k+1) :: drop(k+2), where getElem(k+1) of the mapped list is f(finRange[k+1]) = f(⟨k+1, ...⟩).

Alternatively, apply finRange_map_split twice: first at k, then at ⟨k+1, ...⟩. But the second application is on the full list, not the drop.

Simplest: use ext_getElem? to show both sides are equal element by element. For i < k: both give take[i]. For i = k: both give f(k). For i = k+1: both give f(k+1). For i > k+1: both give drop[i-(k+2)] offset appropriately.
-/
lemma finRange_map_split_two {n : ℕ} {α : Type*} (f : Fin (n + 1) → α)
    (k : Fin (n + 1)) (hk : k.val + 1 ≤ n) :
    (List.finRange (n + 1)).map f =
      ((List.finRange (n + 1)).map f).take k.val ++
      [f k, f ⟨k.val + 1, by omega⟩] ++
      ((List.finRange (n + 1)).map f).drop (k.val + 2) := by
  refine' List.ext_get _ _ <;> simp +decide [ hk ];
  · omega;
  · intro i hi₁ hi₂; rcases lt_or_ge i k.val <;> simp_all +decide [ List.getElem_append ] ;
    rcases eq_or_lt_of_le ‹_› with ( rfl | hk' ) <;> simp_all +decide [ List.getElem_cons ];
    lia

/-
PROBLEM
Simulation case: right interior move.
    Head moves from position h to h+1, cells at h and h+1 change.
    Uses two CS derivation steps (step 1: remove head from h; step 2: place head at h+1).

PROVIDED SOLUTION
The proof uses two CS_transforms steps.

Define the intermediate sentential form w_mid :=
  (encodeExtCfg ecfg₁).take h ++ [cellSym lb₁ false none a' t₁, cellSym false rb₂ none (ecfg₁.tape h₊₁) (ecfg₁.input h₊₁)] ++ (encodeExtCfg ecfg₁).drop (h+2)
where lb₁ = decide(h=0), rb₂ = decide(h+1=n), h₊₁ = ⟨h+1, ...⟩.

Step 1: encodeExtCfg ecfg₁ →CS w_mid
  Using finRange_map_split_two, encodeExtCfg ecfg₁ = take(h) ++ [cell_h, cell_h+1] ++ drop(h+2).
  cell_h = cellSym lb₁ false (some state) (tape h) (input h)  -- where decide(h=n) = false since h < n
  cell_h+1 = cellSym false rb₂ none (tape h₊₁) (input h₊₁)  -- decide(h+1=0) = false, q = none since h+1 ≠ h

  Apply rule sim_right_interior_step1_mem with q=state, a=tape[h], output=[cellSym lb₁ false none a' t₁], context_right=[cell_h+1].
  u = take(h), v = drop(h+2).

Step 2: w_mid →CS encodeExtCfg ecfg₂
  w_mid = take(h) ++ [cellSym lb₁ false none a' t₁] ++ [cellSym false rb₂ none (tape h₊₁) (input h₊₁)] ++ drop(h+2)

  Apply rule sim_right_interior_step2_mem with context_left=[cellSym lb₁ false none a' t₁], input=cell_h+1.
  Output = [cellSym false rb₂ (some q') (tape h₊₁) (input h₊₁)].

  After step 2: take(h) ++ [cellSym lb₁ false none a' t₁, cellSym false rb₂ (some q') (tape h₊₁) (input h₊₁)] ++ drop(h+2)

  This equals encodeExtCfg ecfg₂ because:
  - take(h) same (positions i < h: tape unchanged, head marker absent for both)
  - At h: cellSym lb₁ false none a' (input h) -- no head (h ≠ h+1), tape=a' (update_same)
  - At h+1: cellSym false rb₂ (some q') (tape h₊₁) (input h₊₁) -- head here, tape unchanged (update_noteq)
  - drop(h+2) same (positions i > h+1: tape unchanged, head marker absent)

Use ReflTransGen.tail or trans to compose the two steps.

For showing take(h)/drop(h+2) are the same for ecfg₁ and ecfg₂:
use ext_getElem? and the facts about Function.update_noteq, the if-then-else on head position.

Three-step simulation for right interior move.

Set h = ecfg₁.head. We use finRange_map_split_two to decompose encodeExtCfg at positions h and h+1.

Key boundary facts: decide(h.val = n) = false (since h_lt), decide(h.val + 1 = 0) = false.

Step 1 (CS_transforms): Apply rule sim_right_interior_step1_mem. This replaces cell(lb₁, false, some q, a, t₁) at position h with cellPending(lb₁, false, q', a', t₁). The right context is the cell at position h+1 (which has q=none since h+1 ≠ h).

Step 2 (CS_transforms): Apply rule sim_right_interior_step2_mem. The cellPending is now in context_left. The input nonterminal is the cell at position h+1. It gets replaced with cell(false, rb₂, some q', b, t₂).

Step 3 (CS_transforms): Apply rule pending_resolution_rule_mem. This replaces cellPending(lb₁, false, q', a', t₁) with cell(lb₁, false, none, a', t₁).

Compose with ReflTransGen.

To show encodeExtCfg ecfg₁ equals the start form and encodeExtCfg ecfg₂ equals the end form, use finRange_map_split_two and ext_get to show the lists are equal element by element. Use Function.update_apply to handle tape changes.
-/
set_option maxHeartbeats 800000 in
lemma sim_step_right_interior {n : ℕ}
    (ecfg₁ : ExtCfg T Γ Λ n)
    (q' : Λ) (a' : Γ)
    (h_lt : ecfg₁.head.val < n)
    (h_trans : (q', a', LBA.Dir.right) ∈ M.transition ecfg₁.state (ecfg₁.tape ecfg₁.head)) :
    let head₂ : Fin (n + 1) := ⟨ecfg₁.head.val + 1, by omega⟩
    let ecfg₂ : ExtCfg T Γ Λ n := ⟨q', head₂,
      Function.update ecfg₁.tape ecfg₁.head a', ecfg₁.input⟩
    CS_derives (myhillGrammar M embed)
      (encodeExtCfg ecfg₁)
      (encodeExtCfg ecfg₂) := by
  refine' Relation.ReflTransGen.trans _ _;
  exact ( encodeExtCfg ecfg₁ ).take ecfg₁.head.val ++ [ cellPendingSym ( decide ( ecfg₁.head.val = 0 ) ) false q' a' ( ecfg₁.input ecfg₁.head ), cellSym false ( decide ( ecfg₁.head.val + 1 = n ) ) none ( ecfg₁.tape ⟨ ecfg₁.head.val + 1, by linarith ⟩ ) ( ecfg₁.input ⟨ ecfg₁.head.val + 1, by linarith ⟩ ) ] ++ ( encodeExtCfg ecfg₁ ).drop ( ecfg₁.head.val + 2 );
  · have h_finRange_map_split_two : encodeExtCfg ecfg₁ = (encodeExtCfg ecfg₁).take ecfg₁.head.val ++ [cellSym (decide (ecfg₁.head.val = 0)) false (some ecfg₁.state) (ecfg₁.tape ecfg₁.head) (ecfg₁.input ecfg₁.head), cellSym false (decide (ecfg₁.head.val + 1 = n)) none (ecfg₁.tape ⟨ecfg₁.head.val + 1, by linarith⟩) (ecfg₁.input ⟨ecfg₁.head.val + 1, by linarith⟩)] ++ (encodeExtCfg ecfg₁).drop (ecfg₁.head.val + 2) := by
      convert finRange_map_split_two _ _ _;
      all_goals norm_num [ Fin.ext_iff, h_lt.ne ];
      exact h_lt;
    rw [ h_finRange_map_split_two ];
    apply_rules [ Relation.ReflTransGen.single ];
    refine' ⟨ _, _, _, _, _ ⟩;
    exact ⟨ [ ], MyhillNT.cell ( decide ( ecfg₁.head.val = 0 ) ) false ( some ecfg₁.state ) ( ecfg₁.tape ecfg₁.head ) ( ecfg₁.input ecfg₁.head ), [ cellSym false ( decide ( ecfg₁.head.val + 1 = n ) ) none ( ecfg₁.tape ⟨ ecfg₁.head.val + 1, by linarith ⟩ ) ( ecfg₁.input ⟨ ecfg₁.head.val + 1, by linarith ⟩ ) ], [ cellPendingSym ( decide ( ecfg₁.head.val = 0 ) ) false q' a' ( ecfg₁.input ecfg₁.head ) ] ⟩;
    exact ( encodeExtCfg ecfg₁ ).take ecfg₁.head.val;
    exact ( encodeExtCfg ecfg₁ ).drop ( ecfg₁.head.val + 2 );
    · apply_rules [ sim_right_interior_step1_mem ];
    · simp +decide [ List.take_append, List.drop_append ];
      simp +decide [ List.take_take, List.drop_drop, min_eq_left ( show ( ecfg₁.head : ℕ ) ≤ ( encodeExtCfg ecfg₁ ).length from by simp +decide [ encodeExtCfg ] ) ];
  · have h_step2 : CS_transforms (myhillGrammar M embed)
      ((encodeExtCfg ecfg₁).take ecfg₁.head.val ++
       [cellPendingSym (decide (ecfg₁.head.val = 0)) false q' a' (ecfg₁.input ecfg₁.head),
        cellSym false (decide (ecfg₁.head.val + 1 = n)) none (ecfg₁.tape ⟨ecfg₁.head.val + 1, by linarith⟩) (ecfg₁.input ⟨ecfg₁.head.val + 1, by linarith⟩)] ++
       (encodeExtCfg ecfg₁).drop (ecfg₁.head.val + 2))
      ((encodeExtCfg ecfg₁).take ecfg₁.head.val ++
       [cellPendingSym (decide (ecfg₁.head.val = 0)) false q' a' (ecfg₁.input ecfg₁.head),
        cellSym false (decide (ecfg₁.head.val + 1 = n)) (some q') (ecfg₁.tape ⟨ecfg₁.head.val + 1, by linarith⟩) (ecfg₁.input ⟨ecfg₁.head.val + 1, by linarith⟩)] ++
       (encodeExtCfg ecfg₁).drop (ecfg₁.head.val + 2)) := by
         use ⟨[cellPendingSym (decide (ecfg₁.head.val = 0)) false q' a' (ecfg₁.input ecfg₁.head)], MyhillNT.cell false (decide (ecfg₁.head.val + 1 = n)) none (ecfg₁.tape ⟨ecfg₁.head.val + 1, by linarith⟩) (ecfg₁.input ⟨ecfg₁.head.val + 1, by linarith⟩), [], [cellSym false (decide (ecfg₁.head.val + 1 = n)) (some q') (ecfg₁.tape ⟨ecfg₁.head.val + 1, by linarith⟩) (ecfg₁.input ⟨ecfg₁.head.val + 1, by linarith⟩)]⟩;
         use (encodeExtCfg ecfg₁).take ecfg₁.head.val, (encodeExtCfg ecfg₁).drop (ecfg₁.head.val + 2);
         simp +decide [ myhillGrammar ];
         apply sim_right_interior_step2_mem;
    refine' .single _ |> Relation.ReflTransGen.trans <| _;
    exact ( encodeExtCfg ecfg₁ ).take ecfg₁.head.val ++ [ cellPendingSym ( decide ( ecfg₁.head.val = 0 ) ) false q' a' ( ecfg₁.input ecfg₁.head ), cellSym false ( decide ( ecfg₁.head.val + 1 = n ) ) ( some q' ) ( ecfg₁.tape ⟨ ecfg₁.head.val + 1, by linarith ⟩ ) ( ecfg₁.input ⟨ ecfg₁.head.val + 1, by linarith ⟩ ) ] ++ ( encodeExtCfg ecfg₁ ).drop ( ecfg₁.head.val + 2 );
    · exact h_step2;
    · refine' .single _ |> Relation.ReflTransGen.trans <| _;
      exact ( encodeExtCfg ecfg₁ ).take ecfg₁.head.val ++ [ cellSym ( decide ( ecfg₁.head.val = 0 ) ) false none a' ( ecfg₁.input ecfg₁.head ), cellSym false ( decide ( ecfg₁.head.val + 1 = n ) ) ( some q' ) ( ecfg₁.tape ⟨ ecfg₁.head.val + 1, by linarith ⟩ ) ( ecfg₁.input ⟨ ecfg₁.head.val + 1, by linarith ⟩ ) ] ++ ( encodeExtCfg ecfg₁ ).drop ( ecfg₁.head.val + 2 );
      · refine' ⟨ _, _, _, _, _ ⟩;
        exact ⟨ [ ], MyhillNT.cellPending ( decide ( ecfg₁.head.val = 0 ) ) false q' a' ( ecfg₁.input ecfg₁.head ), [ ], [ cellSym ( decide ( ecfg₁.head.val = 0 ) ) false none a' ( ecfg₁.input ecfg₁.head ) ] ⟩;
        exact ( encodeExtCfg ecfg₁ ).take ecfg₁.head.val;
        exact [ cellSym false ( decide ( ecfg₁.head.val + 1 = n ) ) ( some q' ) ( ecfg₁.tape ⟨ ecfg₁.head.val + 1, by linarith ⟩ ) ( ecfg₁.input ⟨ ecfg₁.head.val + 1, by linarith ⟩ ) ] ++ ( encodeExtCfg ecfg₁ ).drop ( ecfg₁.head.val + 2 );
        · exact pending_resolution_rule_mem M embed q' a' ( ecfg₁.input ecfg₁.head ) ( decide ( ecfg₁.head.val = 0 ) ) false;
        · simp +decide [ List.append_assoc ];
      · convert Relation.ReflTransGen.refl using 1;
        refine' List.ext_get _ _ <;> simp +decide [ encodeExtCfg ];
        · omega;
        · intro i hi₁ hi₂; rcases lt_trichotomy i ( ecfg₁.head.val ) with hi₃ | rfl | hi₃ <;> simp_all +decide [ List.getElem_append ] ;
          · grind +splitImp;
          · simp +decide [ Function.update_apply, h_lt.ne ];
          · rcases eq_or_ne i ( ecfg₁.head.val + 1 ) with rfl | hi₄ <;> simp_all +decide [ List.getElem_cons ];
            · simp +decide [ Function.update_apply, Fin.ext_iff ];
            · split_ifs <;> simp_all +decide [ Nat.sub_sub, add_assoc ];
              · linarith;
              · omega;
              · omega;
              · grind;
              · grind

/-
PROVIDED SOLUTION
This is the mirror of sim_step_right_interior (proved immediately above). Follow the EXACT same proof structure but with positions k = h-1 and h instead of h and h+1.

Set k = ⟨ecfg₁.head.val - 1, ...⟩. Note k.val + 1 = ecfg₁.head.val.

Three steps:
Step 1: Apply sim_left_interior_step1_mem. Context_left is cell at k (has q=none, rb=false). Input is cell at h (has some state). Output is cellPending at h.
Step 2: Apply sim_left_interior_step2_mem. Input is cell at k. Context_right is cellPending at h. Output replaces cell at k with cell(some q').
Step 3: Apply pending_resolution_rule_mem. Replace cellPending at h with cell(none, a').

The structure is identical to sim_step_right_interior above: use finRange_map_split_two to split, show three CS_transforms, compose them, then show the final result equals encodeExtCfg ecfg₂ using ext_get.
-/
set_option maxHeartbeats 800000 in
lemma sim_step_left_interior {n : ℕ}
    (ecfg₁ : ExtCfg T Γ Λ n)
    (q' : Λ) (a' : Γ)
    (h_gt : 0 < ecfg₁.head.val)
    (h_trans : (q', a', LBA.Dir.left) ∈ M.transition ecfg₁.state (ecfg₁.tape ecfg₁.head)) :
    let head₂ : Fin (n + 1) := ⟨ecfg₁.head.val - 1, by omega⟩
    let ecfg₂ : ExtCfg T Γ Λ n := ⟨q', head₂,
      Function.update ecfg₁.tape ecfg₁.head a', ecfg₁.input⟩
    CS_derives (myhillGrammar M embed)
      (encodeExtCfg ecfg₁)
      (encodeExtCfg ecfg₂) := by
  obtain ⟨head₁, head₂, h_head⟩ : ∃ head₁ head₂ : Fin (n + 1), head₁.val + 1 = head₂.val ∧ head₂ = ecfg₁.head := by
    exact ⟨ ⟨ ecfg₁.head - 1, by omega ⟩, ecfg₁.head, Nat.succ_pred_eq_of_pos h_gt, rfl ⟩
  generalize_proofs at *; (
  -- Apply the sim_left_interior_step1_mem lemma to get the first step in the derivation.
  have h_step1 : CS_transforms (myhillGrammar M embed)
    (encodeExtCfg ecfg₁)
    (List.take head₁.val (encodeExtCfg ecfg₁) ++
     [cellSym (decide (head₁.val = 0)) false none (ecfg₁.tape head₁) (ecfg₁.input head₁),
      cellPendingSym false (decide (head₂.val = n)) q' a' (ecfg₁.input head₂)] ++
     List.drop (head₁.val + 2) (encodeExtCfg ecfg₁)) := by
       have h_step1 : CS_transforms (myhillGrammar M embed)
         (List.take head₁.val (encodeExtCfg ecfg₁) ++
          [cellSym (decide (head₁.val = 0)) false none (ecfg₁.tape head₁) (ecfg₁.input head₁),
           cellSym false (decide (head₂.val = n)) (some ecfg₁.state) (ecfg₁.tape head₂) (ecfg₁.input head₂)] ++
          List.drop (head₁.val + 2) (encodeExtCfg ecfg₁))
         (List.take head₁.val (encodeExtCfg ecfg₁) ++
          [cellSym (decide (head₁.val = 0)) false none (ecfg₁.tape head₁) (ecfg₁.input head₁),
           cellPendingSym false (decide (head₂.val = n)) q' a' (ecfg₁.input head₂)] ++
          List.drop (head₁.val + 2) (encodeExtCfg ecfg₁)) := by
            have h_step1 : ⟨[cellSym (decide (head₁.val = 0)) false none (ecfg₁.tape head₁) (ecfg₁.input head₁)],
                          MyhillNT.cell false (decide (head₂.val = n)) (some ecfg₁.state) (ecfg₁.tape head₂) (ecfg₁.input head₂), [],
                          [cellPendingSym false (decide (head₂.val = n)) q' a' (ecfg₁.input head₂)]⟩ ∈ myhillAllRules M embed := by
                            apply sim_left_interior_step1_mem; aesop;
            generalize_proofs at *; (
            use ⟨[cellSym (decide (head₁.val = 0)) false none (ecfg₁.tape head₁) (ecfg₁.input head₁)], MyhillNT.cell false (decide (head₂.val = n)) (some ecfg₁.state) (ecfg₁.tape head₂) (ecfg₁.input head₂), [], [cellPendingSym false (decide (head₂.val = n)) q' a' (ecfg₁.input head₂)]⟩, take (head₁.val) (encodeExtCfg ecfg₁), drop (head₁.val + 2) (encodeExtCfg ecfg₁) ; aesop;)
       generalize_proofs at *; (
       convert h_step1 using 1
       generalize_proofs at *; (
       convert finRange_map_split_two _ _ _ using 2
       generalize_proofs at *; (
       congr! 2
       generalize_proofs at *; (
       congr! 2
       generalize_proofs at *; (
       lia);
       grind +ring);
       grind);
       lia))
  generalize_proofs at *; (
  -- Apply the sim_left_interior_step2_mem lemma to get the second step in the derivation.
  have h_step2 : CS_transforms (myhillGrammar M embed)
    (List.take head₁.val (encodeExtCfg ecfg₁) ++
     [cellSym (decide (head₁.val = 0)) false none (ecfg₁.tape head₁) (ecfg₁.input head₁),
      cellPendingSym false (decide (head₂.val = n)) q' a' (ecfg₁.input head₂)] ++
     List.drop (head₁.val + 2) (encodeExtCfg ecfg₁))
    (List.take head₁.val (encodeExtCfg ecfg₁) ++
     [cellSym (decide (head₁.val = 0)) false (some q') (ecfg₁.tape head₁) (ecfg₁.input head₁),
      cellPendingSym false (decide (head₂.val = n)) q' a' (ecfg₁.input head₂)] ++
     List.drop (head₁.val + 2) (encodeExtCfg ecfg₁)) := by
       have := sim_left_interior_step2_mem M embed q' a' (ecfg₁.input head₁) (ecfg₁.input head₂) (decide (head₁.val = 0)) (decide (head₂.val = n)) none (ecfg₁.tape head₁)
       generalize_proofs at *; (
       exact ⟨ _, _, _, by aesop ⟩)
  generalize_proofs at *; (
  -- Apply the pending_resolution_rule_mem lemma to get the third step in the derivation.
  have h_step3 : CS_transforms (myhillGrammar M embed)
    (List.take head₁.val (encodeExtCfg ecfg₁) ++
     [cellSym (decide (head₁.val = 0)) false (some q') (ecfg₁.tape head₁) (ecfg₁.input head₁),
      cellPendingSym false (decide (head₂.val = n)) q' a' (ecfg₁.input head₂)] ++
     List.drop (head₁.val + 2) (encodeExtCfg ecfg₁))
    (List.take head₁.val (encodeExtCfg ecfg₁) ++
     [cellSym (decide (head₁.val = 0)) false (some q') (ecfg₁.tape head₁) (ecfg₁.input head₁),
      cellSym false (decide (head₂.val = n)) none a' (ecfg₁.input head₂)] ++
     List.drop (head₁.val + 2) (encodeExtCfg ecfg₁)) := by
       use ⟨[], MyhillNT.cellPending false (decide (head₂.val = n)) q' a' (ecfg₁.input head₂), [], [cellSym false (decide (head₂.val = n)) none a' (ecfg₁.input head₂)]⟩, List.take head₁.val (encodeExtCfg ecfg₁) ++ [cellSym (decide (head₁.val = 0)) false (some q') (ecfg₁.tape head₁) (ecfg₁.input head₁)], List.drop (head₁.val + 2) (encodeExtCfg ecfg₁);
       exact ⟨ pending_resolution_rule_mem M embed q' a' ( ecfg₁.input head₂ ) false ( decide ( head₂.val = n ) ), by simp +decide [ List.append_assoc ] ⟩
  generalize_proofs at *; (
  convert CS_deri_of_deri_deri ( CS_deri_of_deri_deri ( CS_deri_of_tran h_step1 ) ( CS_deri_of_tran h_step2 ) ) ( CS_deri_of_tran h_step3 ) using 1
  generalize_proofs at *; (
  refine' List.ext_get _ _ <;> simp +decide [ * ];
  · unfold encodeExtCfg; simp +decide [ List.length_map, List.length_finRange ] ; omega;
  · intro i hi₁ hi₂; rcases lt_trichotomy i head₁.val with hi | rfl | hi <;> simp_all +decide [ List.getElem_append ] ;
    · grind +locals;
    · unfold encodeExtCfg; simp +decide [ List.getElem_map, List.getElem_finRange ] ;
      grind;
    · rcases i with ( _ | i ) <;> simp_all +decide [ List.getElem_append ] ;
      unfold encodeExtCfg at * ; simp_all +decide [ List.getElem_cons ] ;
      grind +splitImp)))))

theorem sim_step_derives {n : ℕ}
    (ecfg₁ ecfg₂ : ExtCfg T Γ Λ n)
    (h_input : ecfg₁.input = ecfg₂.input)
    (h_step : ∃ q' a' d,
      (q', a', d) ∈ M.transition ecfg₁.state (ecfg₁.tape ecfg₁.head) ∧
      ecfg₂.state = q' ∧
      ecfg₂.tape = Function.update ecfg₁.tape ecfg₁.head a' ∧
      ecfg₂.head = (LBA.BoundedTape.moveHead ⟨ecfg₁.tape, ecfg₁.head⟩ d).head) :
    CS_derives (myhillGrammar M embed)
      (encodeExtCfg ecfg₁)
      (encodeExtCfg ecfg₂) := by
  obtain ⟨ q', a', d, hd, h₁, h₂, h₃ ⟩ := h_step; ( rcases d with ( _ | _ | _ ) );
  · -- Since the head moves left, we have two cases: ecfg₁.head.val > 0 or ecfg₁.head.val = 0.
    by_cases h_head_pos : 0 < ecfg₁.head.val;
    · convert sim_step_left_interior M embed ecfg₁ q' a' h_head_pos hd using 1;
      convert encodeExtCfg_ext _ _ _ ; aesop;
      all_goals try infer_instance;
      simp_all +decide [ LBA.BoundedTape.moveHead ];
    · convert sim_step_single_cell M embed ecfg₁ q' a' _ _ using 1;
      · cases ecfg₁ ; cases ecfg₂ ; aesop;
      · tauto;
      · convert sim_left_boundary_rule_mem M embed ecfg₁.state q' ( ecfg₁.tape ecfg₁.head ) a' ( ecfg₁.input ecfg₁.head ) _ hd using 1;
        aesop;
  · by_cases h : ecfg₁.head.val = n <;> simp_all +decide [ LBA.BoundedTape.moveHead ];
    · convert sim_step_single_cell M embed ecfg₁ q' a' _ _ using 1;
      · exact congr_arg _ ( by cases ecfg₂; aesop );
      · lia;
      · grind +suggestions;
    · convert sim_step_right_interior M embed ecfg₁ q' a' _ hd using 1;
      all_goals norm_num [ encodeExtCfg, h_input.symm, h₁, h₂, h₃ ];
      grind;
      exact lt_of_le_of_ne ( Nat.le_of_lt_succ ( Fin.is_lt _ ) ) h;
  · convert sim_step_single_cell M embed ecfg₁ q' a' _ _ using 1;
    · cases ecfg₂ ; aesop;
    · grind +splitImp;
    · convert sim_stay_rule_mem M embed ecfg₁.state q' ( ecfg₁.tape ecfg₁.head ) a' ( ecfg₁.input ecfg₁.head ) _ _ hd using 1

/-! ### Phase 3: Cleanup -/

/-
PROBLEM
Split a mapped finRange list at position k.

PROVIDED SOLUTION
Use List.take_append_drop and List.drop_eq_getElem_cons.
conv_lhs => rw [← List.take_append_drop k.val ((List.finRange (n+1)).map f)]
rw [List.drop_eq_getElem_cons (by simp; exact k.isLt)]
Then we need to show the getElem equals f k. Use List.getElem_map and List.getElem_finRange to show that ((finRange (n+1)).map f)[k.val] = f k.
-/
lemma finRange_map_split {α : Type*} (f : Fin (n + 1) → α) (k : Fin (n + 1)) :
    (List.finRange (n + 1)).map f =
      ((List.finRange (n + 1)).map f).take k.val ++
      [f k] ++
      ((List.finRange (n + 1)).map f).drop (k.val + 1) := by
  -- By definition of `List.take` and `List.drop`, we can split the list into the first `k` elements, the `k`-th element, and the rest.
  have h_split : List.take (k.val + 1) (List.finRange (n + 1) |>.map f) = List.take k.val (List.finRange (n + 1) |>.map f) ++ [f k] := by
    simp +decide [ List.take_add_one, List.finRange_succ ];
    induction k using Fin.inductionOn <;> simp_all +decide [ List.finRange_succ ];
  rw [ ← h_split, List.take_append_drop ]

/-
PROBLEM
Accept step: replace the head cell with a terminal.

PROVIDED SOLUTION
First, use finRange_map_split to decompose encodeExtCfg ecfg at position ecfg.head:
encodeExtCfg ecfg = (encodeExtCfg ecfg).take head ++ [cell_at_head] ++ (encodeExtCfg ecfg).drop (head + 1)

where cell_at_head = symbol.nonterminal (MyhillNT.cell lb rb (some ecfg.state) (ecfg.tape ecfg.head) (ecfg.input ecfg.head))
with lb = decide (head = 0) and rb = decide (head = n).

Since the cell at the head position has q = some ecfg.state (because head = ecfg.head), we can apply the accept rule:
⟨[], .cell lb rb (some ecfg.state) (ecfg.tape ecfg.head) (ecfg.input ecfg.head), [], [terminal (ecfg.input ecfg.head)]⟩

with u = take part, v = drop part.

Use accept_rule_mem M embed ecfg.state h_accept for the rule membership.

The key is to show that the specific cell in encodeExtCfg at position head is cellSym lb rb (some ecfg.state) ..., which follows from the definition of encodeExtCfg where if i = ecfg.head then q = some ecfg.state.
-/
lemma cleanup_accept_transforms {n : ℕ}
    (ecfg : ExtCfg T Γ Λ n)
    (h_accept : M.accept ecfg.state = true) :
    CS_transforms (myhillGrammar M embed)
      (encodeExtCfg ecfg)
      ((encodeExtCfg ecfg).take ecfg.head.val ++
       [symbol.terminal (ecfg.input ecfg.head)] ++
       (encodeExtCfg ecfg).drop (ecfg.head.val + 1)) := by
  have h_rule : ⟨[], MyhillNT.cell (decide (ecfg.head = 0)) (decide (ecfg.head = n)) (some ecfg.state) (ecfg.tape ecfg.head) (ecfg.input ecfg.head), [], [symbol.terminal (ecfg.input ecfg.head)]⟩ ∈ myhillAllRules M embed := by
    apply_rules [ accept_rule_mem, h_accept ];
  have h_transform : encodeExtCfg ecfg = (take (ecfg.head.val) (encodeExtCfg ecfg)) ++ [cellSym (decide (ecfg.head = 0)) (decide (ecfg.head = n)) (some ecfg.state) (ecfg.tape ecfg.head) (ecfg.input ecfg.head)] ++ (drop (ecfg.head.val + 1) (encodeExtCfg ecfg)) := by
    convert finRange_map_split _ _ using 2;
    unfold encodeExtCfg; aesop;
  exact ⟨ _, _, _, h_rule, by simpa [ eq_comm ] using h_transform, by simp +decide [ eq_comm ] ⟩

/-
PROBLEM
From an accepting configuration, derive the terminal word.

PROVIDED SOLUTION
The proof has 3 phases:

Phase A: Apply cleanup_accept_transforms at head position:
  encodeExtCfg ecfg → prefix ++ [terminal (input head)] ++ suffix
  where prefix = take head (encodeExtCfg ecfg), suffix = drop (head+1) (encodeExtCfg ecfg)

Phase B: Propagate rightward using propagate_right_list.
  After accept step, suffix consists of cells with q=none. We need to convert them to terminals.
  Express suffix as a list of (lb, rb, a, t) tuples and apply propagate_right_list.

Phase C: Propagate leftward using propagate_left_list.
  After accept step, prefix consists of cells with q=none. We need to convert them to terminals.
  Express prefix as a list of (lb, rb, a, t) tuples and apply propagate_left_list.

The tricky part is showing that:
1. The prefix cells in encodeExtCfg (positions 0..head-1) are all cells with q=none
2. The suffix cells in encodeExtCfg (positions head+1..n) are all cells with q=none
3. After cleanup, the result matches (finRange (n+1)).map terminal

The cells at positions other than head have q=none because `if i = ecfg.head then some ecfg.state else none` evaluates to none when i ≠ head.

To connect with propagate_right_list and propagate_left_list, express the prefix and suffix as mapped lists of tuples. This requires showing that take/drop of the encoded list can be written as maps of lists of tuples.

An alternative approach: express the cleanup process entirely using the propagate lemmas without going through encodeExtCfg decomposition. Use the accept step to get one terminal, then alternately propagate left and right.

The simplest approach might be:
1. Apply accept_transforms to get one terminal at head
2. Apply propagate_right_list for the right suffix
3. Apply propagate_left_list for the left prefix
4. Show the result equals the target

For steps 2-3, we need to express the prefix and suffix in the right form. Use finRange_map_split and List.take/drop of the mapped finRange.
-/
theorem cleanup_derives {n : ℕ}
    (ecfg : ExtCfg T Γ Λ n)
    (h_accept : M.accept ecfg.state = true) :
    CS_derives (myhillGrammar M embed)
      (encodeExtCfg ecfg)
      ((List.finRange (n + 1)).map fun i => symbol.terminal (ecfg.input i)) := by
  have h_propagate_right : CS_derives (myhillGrammar M embed)
    ((encodeExtCfg ecfg).take ecfg.head.val ++ [symbol.terminal (ecfg.input ecfg.head)] ++ (encodeExtCfg ecfg).drop (ecfg.head.val + 1))
    ((encodeExtCfg ecfg).take ecfg.head.val ++ [symbol.terminal (ecfg.input ecfg.head)] ++ (List.finRange (n + 1) |>.map (fun i => symbol.terminal (ecfg.input i)) |>.drop (ecfg.head.val + 1))) := by
      convert propagate_right_list _ _ _ _ _;
      any_goals exact ( List.finRange ( n + 1 ) |>.drop ( ecfg.head.val + 1 ) |>.map fun i => ( decide ( i.val = 0 ), decide ( i.val = n ), ecfg.tape i, ecfg.input i ) );
      · refine' List.ext_get _ _ <;> simp +decide [ encodeExtCfg ];
        exact fun i hi => ne_of_gt ( Nat.lt_of_lt_of_le ( Nat.lt_succ_self _ ) ( Nat.le_add_right _ _ ) );
      · refine' List.ext_get _ _ <;> simp +decide [ List.get ];
  have h_propagate_left : CS_derives (myhillGrammar M embed)
    ((encodeExtCfg ecfg).take ecfg.head.val ++ [symbol.terminal (ecfg.input ecfg.head)] ++ (List.finRange (n + 1) |>.map (fun i => symbol.terminal (ecfg.input i)) |>.drop (ecfg.head.val + 1)))
    ((List.finRange (n + 1) |>.map (fun i => symbol.terminal (ecfg.input i)))) := by
      have h_propagate_left : ∀ (cells : List (Bool × Bool × Γ × T)), CS_derives (myhillGrammar M embed)
        ((cells.map (fun ⟨lb, rb, a, t⟩ => cellSym lb rb none a t) : List (symbol T (MyhillNT T Γ Λ))) ++ [symbol.terminal (ecfg.input ecfg.head)] ++ (List.finRange (n + 1) |>.map (fun i => symbol.terminal (ecfg.input i)) |>.drop (ecfg.head.val + 1)))
        ((cells.map (fun ⟨_, _, _, t⟩ => symbol.terminal t) : List (symbol T (MyhillNT T Γ Λ))) ++ [symbol.terminal (ecfg.input ecfg.head)] ++ (List.finRange (n + 1) |>.map (fun i => symbol.terminal (ecfg.input i)) |>.drop (ecfg.head.val + 1))) := by
          intro cells
          apply propagate_left_list;
      convert h_propagate_left ( List.map ( fun i => ( decide ( i.val = 0 ), decide ( i.val = n ), ecfg.tape i, ecfg.input i ) ) ( List.take ecfg.head ( List.finRange ( n + 1 ) ) ) ) using 1;
      · simp +decide [ encodeExtCfg ];
        refine' List.ext_get _ _ <;> simp +decide [ cellSym ];
        exact fun i hi => ne_of_lt hi;
      · refine' List.ext_get _ _ <;> simp +decide [ List.get ];
        · grind;
        · intro i hi₁ hi₂; by_cases hi₃ : i < ecfg.head.val <;> simp_all +decide [ List.getElem_append, List.getElem_cons ] ;
          split_ifs <;> simp_all +decide [ Nat.sub_eq_iff_eq_add' hi₃ ];
          congr 2 ; omega;
  exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (cleanup_accept_transforms M embed ecfg h_accept)) (Relation.ReflTransGen.trans h_propagate_right h_propagate_left)

/-! ### Correctness -/

/-
PROBLEM
Lifting NLBA.Reaches to CS_derives via ExtCfg.

PROVIDED SOLUTION
By induction on h_reaches : NLBA.Reaches M cfg₁ cfg₂ (which is ReflTransGen of NLBA.Step).

Base case (refl): cfg₁ = cfg₂, so the encodings are equal. Use ReflTransGen.refl.

Step case: cfg₁ →(Step) cfg_mid →*(Reaches) cfg₂. By IH, we have CS_derives from encoding of cfg_mid to encoding of cfg₂.

For the single step cfg₁ →(Step) cfg_mid: unfold NLBA.Step to get ∃ q' a' d, (q', a', d) ∈ M.transition cfg₁.state cfg₁.tape.read ∧ cfg_mid = ⟨q', (cfg₁.tape.write a').moveHead d⟩.

Apply sim_step_derives with:
- ecfg₁ = ⟨cfg₁.state, cfg₁.tape.head, cfg₁.tape.contents, input_fn⟩
- ecfg₂ = ⟨cfg_mid.state, cfg_mid.tape.head, cfg_mid.tape.contents, input_fn⟩
- h_input = rfl (both have input_fn)
- h_step = ⟨q', a', d, h_trans, eq for state, eq for tape, eq for head⟩

The tape update: cfg_mid.tape = (cfg₁.tape.write a').moveHead d
- (cfg₁.tape.write a').contents = Function.update cfg₁.tape.contents cfg₁.tape.head a'
- (cfg₁.tape.write a').moveHead d has same contents as cfg₁.tape.write a'
- BoundedTape.moveHead preserves contents

So cfg_mid.tape.contents = Function.update cfg₁.tape.contents cfg₁.tape.head a'
And cfg_mid.tape.head = ((cfg₁.tape.write a').moveHead d).head = (⟨Function.update ..., cfg₁.tape.head⟩.moveHead d).head which equals (BoundedTape.moveHead ⟨cfg₁.tape.contents, cfg₁.tape.head⟩ d).head since moveHead only changes head, not contents... wait actually write changes contents first, then moveHead changes head. So:
- cfg₁.tape.write a' = ⟨Function.update cfg₁.tape.contents cfg₁.tape.head a', cfg₁.tape.head⟩
- moveHead of that = ⟨Function.update cfg₁.tape.contents cfg₁.tape.head a', new_head⟩

So the BoundedTape in the hypothesis of sim_step_derives should be ⟨cfg₁.tape.contents, cfg₁.tape.head⟩ (=ecfg₁.tape with ecfg₁.head), and we need:
ecfg₂.head = (BoundedTape.moveHead ⟨ecfg₁.tape, ecfg₁.head⟩ d).head

But the actual new head is from (cfg₁.tape.write a').moveHead d which starts with head at cfg₁.tape.head (same as before write). So moveHead ⟨_, cfg₁.tape.head⟩ d gives the correct head. Since write doesn't change head, BoundedTape.moveHead ⟨updated_contents, cfg₁.tape.head⟩ d has same head as BoundedTape.moveHead ⟨original_contents, cfg₁.tape.head⟩ d (moveHead only depends on head position, not contents).

Use ReflTransGen.head or ReflTransGen.trans to compose.
-/
lemma sim_reaches_derives {n : ℕ}
    (input_fn : Fin (n + 1) → T)
    (cfg₁ cfg₂ : LBA.Cfg Γ Λ n)
    (h_reaches : NLBA.Reaches M cfg₁ cfg₂) :
    CS_derives (myhillGrammar M embed)
      (encodeExtCfg (⟨cfg₁.state, cfg₁.tape.head, cfg₁.tape.contents, input_fn⟩ : ExtCfg T Γ Λ n))
      (encodeExtCfg (⟨cfg₂.state, cfg₂.tape.head, cfg₂.tape.contents, input_fn⟩ : ExtCfg T Γ Λ n)) := by
  induction h_reaches;
  · constructor;
  · rename_i h₁ h₂ h₃;
    refine' h₃.trans _;
    convert sim_step_derives M embed _ _ _ _;
    · aesop;
    · rcases h₂ with ⟨ q', a, d, h₁, h₂ ⟩ ; use q', a, d; aesop;

/-
PROBLEM
Forward: if the NLBA accepts `w`, then `w ∈ CS_language (myhillGrammar M embed)`.

PROVIDED SOLUTION
Unfold NLBA.LanguageViaEmbed to get hw_ne : w.map embed ≠ [] and h_acc : NLBA.Accepts M (NLBA.initCfgList M (w.map embed) hw_ne). From h_acc get cfg' with h_reaches and h_accept.

Key: w ≠ [] follows from hw_ne (since w.map embed ≠ [] implies w ≠ []).

The proof chains 3 phases:
1. init_derives: CS_derives from [nt start] to encodeExtCfg (initExtCfg M embed w hw')
2. sim_reaches_derives: CS_derives from initial ExtCfg encoding to final ExtCfg encoding
3. cleanup_derives: CS_derives from final ExtCfg encoding to terminal word

For phase 2, need to connect NLBA.initCfgList with initExtCfg. The initCfgList has state = M.initial, tape.head = 0, tape.contents = fun i => (w.map embed).get ⟨i, ...⟩. The initExtCfg has state = M.initial, head = 0, tape = fun i => embed (w.get ...), input = fun i => w.get ....

Need to show that encodeExtCfg (initExtCfg ...) equals encodeExtCfg of the ExtCfg built from initCfgList.

For the final cleanup, need to show (finRange (n+1)).map (fun i => terminal (input i)) = List.map terminal w when input i = w.get ⟨i, ...⟩.

Use CS_language definition: w ∈ CS_language g iff CS_derives g [nt g.initial] (List.map terminal w).
-/
theorem myhill_forward (w : List T)
    (hw : w ∈ NLBA.LanguageViaEmbed M embed) :
    w ∈ CS_language (myhillGrammar M embed) := by
  by_contra h_contra;
  obtain ⟨hw_ne, cfg', h_reaches, h_accept⟩ := hw;
  refine' h_contra _;
  -- Apply the `cleanup_derives` lemma to get the final cleaned-up encoding.
  have h_cleanup : CS_derives (myhillGrammar M embed) (encodeExtCfg (⟨cfg'.state, cfg'.tape.head, cfg'.tape.contents, fun i => w.get ⟨i, by
    exact lt_of_lt_of_le i.2 ( Nat.succ_le_of_lt ( Nat.sub_lt ( List.length_pos_iff.mpr hw_ne ) zero_lt_one ) ) |> lt_of_lt_of_le <| by simp +decide ;⟩⟩ : ExtCfg T Γ Λ ((List.map embed w).length - 1))) (List.map (fun i => symbol.terminal i) w) := by
    all_goals generalize_proofs at *;
    convert cleanup_derives M embed _ _;
    · refine' List.ext_get _ _ <;> simp +decide [ List.get ];
      rw [ Nat.sub_add_cancel ( List.length_pos_iff.mpr ( by aesop ) ) ];
    · exact h_accept
  generalize_proofs at *;
  have h_init : CS_derives (myhillGrammar M embed) [symbol.nonterminal MyhillNT.start] (encodeExtCfg (⟨M.initial, 0, fun i => (w.map embed).get ⟨i, by
    exact lt_of_lt_of_le i.2 ( Nat.succ_le_of_lt ( Nat.sub_lt ( List.length_pos_iff.mpr hw_ne ) zero_lt_one ) )⟩, fun i => w.get ⟨i, by
    grind⟩⟩ : ExtCfg T Γ Λ ((List.map embed w).length - 1))) := by
    all_goals generalize_proofs at *;
    convert init_derives M embed w _;
    all_goals simp_all +decide [ initExtCfg ];
    all_goals try { exact? };
    · grind;
    · grind;
    · grind
  generalize_proofs at *;
  have h_sim : CS_derives (myhillGrammar M embed) (encodeExtCfg (⟨M.initial, 0, fun i => (w.map embed).get ⟨i, by
    grind⟩, fun i => w.get ⟨i, by
    exact?⟩⟩ : ExtCfg T Γ Λ ((List.map embed w).length - 1))) (encodeExtCfg (⟨cfg'.state, cfg'.tape.head, cfg'.tape.contents, fun i => w.get ⟨i, by
    exact?⟩⟩ : ExtCfg T Γ Λ ((List.map embed w).length - 1))) := by
    all_goals generalize_proofs at *;
    apply sim_reaches_derives M embed (fun i => w.get ⟨i, by
      exact?⟩) (NLBA.initCfgList M (map (⇑embed) w) hw_ne) cfg' h_reaches
  generalize_proofs at *;
  exact Relation.ReflTransGen.trans h_init ( Relation.ReflTransGen.trans h_sim h_cleanup )

/-
PROBLEM
Every Myhill grammar rule applied to a terminal-only sentential form is impossible,
    since CS_transforms requires a nonterminal in the LHS.

PROVIDED SOLUTION
CS_transforms requires the LHS to contain a nonterminal (specifically, the input_nonterminal of the rule). But List.map symbol.terminal w consists entirely of terminal symbols, so it cannot contain any nonterminal. This is a contradiction.

Unfolding CS_transforms gives: ∃ r u v, r ∈ rules ∧ map terminal w = u ++ r.context_left ++ [nt r.input_nonterminal] ++ r.context_right ++ v. This means nonterminal r.input_nonterminal ∈ map terminal w. But every element of map terminal w is of the form terminal t, and nonterminal _ ≠ terminal _. Contradiction.
-/
private lemma no_transforms_from_terminals
    (w : List T)
    (sf : List (symbol T (MyhillNT T Γ Λ)))
    (h : CS_transforms (myhillGrammar M embed) (List.map symbol.terminal w) sf) : False := by
  obtain ⟨ r, u, v, hr, hu, hv ⟩ := h;
  replace hu := congr_arg List.toFinset hu ; rw [ Finset.ext_iff ] at hu ; specialize hu ( symbol.nonterminal r.input_nonterminal ) ; simp_all +decide [ List.mem_append ] ;

/-- Backward: if `w ∈ CS_language (myhillGrammar M embed)`, then the NLBA accepts `w`. -/
theorem myhill_backward (w : List T)
    (hw : w ∈ CS_language (myhillGrammar M embed)) :
    w ∈ NLBA.LanguageViaEmbed M embed := by
  sorry

/-- The Myhill grammar generates exactly the NLBA's language. -/
theorem myhill_language_eq :
    CS_language (myhillGrammar M embed) = NLBA.LanguageViaEmbed M embed := by
  ext w
  exact ⟨myhill_backward M embed w, myhill_forward M embed w⟩

/-- The NLBA language is context-sensitive (assuming finite alphabets). -/
theorem nlba_language_is_CS :
    is_CS (NLBA.LanguageViaEmbed M embed) :=
  ⟨myhillGrammar M embed, myhill_language_eq M embed⟩

end MyhillConstruction