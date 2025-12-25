import Mathlib/Computability/Language

open scoped Classical

namespace Grammars

variable {T : Type _}

def reverseLang (L : Language T) : Language T :=
  fun w : List T => w.reverse ∈ L

def bijemapLang {T' : Type _} (L : Language T) (π : T ≃ T') : Language T' :=
  fun w : List T' => List.map π.symm w ∈ L

def permuteLang (L : Language T) (π : Equiv.Perm T) : Language T :=
  bijemapLang L π

end Grammars
