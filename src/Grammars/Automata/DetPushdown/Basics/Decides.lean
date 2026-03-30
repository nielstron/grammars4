/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Grammars.Automata.DetPushdown.Basics.DPDA

namespace DPDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- Every DCFL is recognized by a DPDA that decides every input. -/
lemma exists_total_dpda :
    ∀ {Q S : Type} [Fintype Q] [Fintype S] (M : DPDA Q T S),
    ∃ (Q' S' : Type) (_ : Fintype Q') (_ : Fintype S') (M' : DPDA Q' T S'),
      M'.acceptsByFinalState = M.acceptsByFinalState ∧ M'.DecidesEveryInput := by
  sorry

end DPDA
