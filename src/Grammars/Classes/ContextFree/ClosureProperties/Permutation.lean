import Grammars.Classes.ContextFree.ClosureProperties.Bijection


/-- The class of context-free languages is closed under permutation of terminals. -/
theorem CF_of_permute_CF {T : Type} (π : equiv.perm T) (L : Language T) :
  is_CF L  →  is_CF (permute_lang L π)  :=
CF_of_bijemap_CF π L
