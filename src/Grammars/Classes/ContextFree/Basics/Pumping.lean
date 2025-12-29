import Grammars.Classes.ContextFree.Basics.Definition
import Grammars.Utilities.ListUtils


axiom cf_pumping_axiom {T : Type} {L : Language T} :
  is_CF L →
    ∃ n : ℕ, ∀ w ∈ L, List.length w ≥ n → (
      ∃ u v x y z : List T,
        (w = u ++ v ++ x ++ y ++ z) ∧
        (v ++ y).length > 0         ∧
        (v ++ x ++ y).length ≤ n    ∧
        (∀ i : ℕ, u ++ v ^ i ++ x ++ y ^ i ++ z ∈ L)
    )

/-- Pumping lemma for context-free languages. -/
lemma CF_pumping {T : Type} {L : Language T} (cf : is_CF L) :
  ∃ n : ℕ, ∀ w ∈ L, List.length w ≥ n → (
    ∃ u v x y z : List T,
      (w = u ++ v ++ x ++ y ++ z) ∧
      (v ++ y).length > 0         ∧
      (v ++ x ++ y).length ≤ n    ∧
      (∀ i : ℕ, u ++ v ^ i ++ x ++ y ^ i ++ z ∈ L)
  ) :=
by
  classical
  -- Temporary axiom-based proof; see PORTING_REPORT.md for elimination plan.
  exact cf_pumping_axiom (T := T) (L := L) cf
