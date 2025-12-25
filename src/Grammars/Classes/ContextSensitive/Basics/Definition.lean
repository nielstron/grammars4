import Grammars.Classes.Unrestricted.Basics.Definition


/-- Transformation rule for a context-sensitive grammar. -/
structure csrule (T : Type) (N : Type) :=
(context_left : List (symbol T N))
(input_nonterminal : N)
(context_right : List (symbol T N))
(output_string : List (symbol T N)) -- !! TODO require non-empty unless `S` → `[]` where `S` is on no right side !!

/-- Context-sensitive grammar that generates words over the alphabet `T` (a type of terminals). -/
structure CS_grammar (T : Type) :=
(nt : Type)                   -- type of nonterminals
(initial : nt)                -- initial symbol
(rules : List (csrule T nt))  -- rewrite rules


variables {T : Type}

/-- One step of context-sensitive transformation. -/
def CS_transforms (g : CS_grammar T) (w₁ w₂ : List (symbol T g.nt)) : Prop :=
∃ r : csrule T g.nt, r ∈ g.rules  ∧  ∃ u v : List (symbol T g.nt), and
  (w₁ = u ++ r.context_left ++ [symbol.nonterminal r.input_nonterminal] ++ r.context_right ++ v)
  (w₂ = u ++ r.context_left ++ r.output_string ++ r.context_right ++ v)

/-- Any number of steps of context-sensitive transformation; reflexive+transitive closure of `CS_transforms`. -/
def CS_derives (g : CS_grammar T) : List (symbol T g.nt) → List (symbol T g.nt) → Prop :=
Relation.refl_trans_gen (CS_transforms g)

/-- The Set of words that can be derived from the initial nonterminal. -/
def CS_language (g : CS_grammar T) : Language T :=
λ w : List T, CS_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal w)

/-- Predicate "is context-sensitive"; defined by existence of a context-sensitive grammar for the given Language. -/
def is_CS (L : Language T) : Prop :=
∃ g : CS_grammar T, CS_language g = L
