import Grammars.Classes.ContextFree.ClosureProperties.Bijection

open Grammars


/-- The class of context-free languages is closed under permutation of terminals. -/
theorem CF_of_permute_CF {T : Type} (π : Equiv.Perm T) (L : Language T) :
  is_CF L  →  is_CF (permuteLang L π)  :=
CF_of_bijemap_CF π L
