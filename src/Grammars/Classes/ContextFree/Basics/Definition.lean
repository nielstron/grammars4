import Grammars.Classes.ContextSensitive.Basics.Definition


/-- Context-free grammar that generates words over the alphabet `T` (a type of terminals). -/
structure CF_grammar (T : Type) where
(nt : Type)                                -- type of nonterminals
(initial : nt)                             -- initial symbol
(rules : List (nt × List (symbol T nt)))   -- rewrite rules


variable {T : Type}

/-- One step of context-free transformation. -/
def CF_transforms (g : CF_grammar T) (w₁ w₂ : List (symbol T g.nt)) : Prop :=
∃ r : g.nt × List (symbol T g.nt), ∃ u v : List (symbol T g.nt),  r ∈ g.rules ∧
  (w₁ = u ++ [symbol.nonterminal r.fst] ++ v) ∧
  (w₂ = u ++ r.snd ++ v)

/-- Any number of steps of context-free transformation; reflexive+transitive closure of `CF_transforms`. -/
def CF_derives (g : CF_grammar T) : List (symbol T g.nt) → List (symbol T g.nt) → Prop :=
Relation.ReflTransGen (CF_transforms g)

/-- Accepts a string (a List of symbols) iff it can be derived from the initial nonterminal. -/
def CF_generates_str (g : CF_grammar T) (s : List (symbol T g.nt)) : Prop :=
CF_derives g [symbol.nonterminal g.initial] s

/-- Accepts a word (a List of terminals) iff it can be derived from the initial nonterminal. -/
def CF_generates (g : CF_grammar T) (w : List T) : Prop :=
CF_generates_str g (List.map symbol.terminal w)

/-- The Set of words that can be derived from the initial nonterminal. -/
def CF_language (g : CF_grammar T) : Language T :=
setOf (CF_generates g)

/-- Predicate "is context-free"; defined by existence of a context-free grammar for the given Language. -/
def is_CF (L : Language T) : Prop :=
∃ g : CF_grammar T, CF_language g = L
