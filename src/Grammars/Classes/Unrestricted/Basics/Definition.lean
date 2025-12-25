import Mathlib.Computability.Language
import Mathlib.Logic.Relation

open Relation

/-- The type of symbols is the disjoint union of terminals and nonterminals. -/
inductive symbol (T : Type) (N : Type) where
  | terminal : T → symbol T N
  | nonterminal : N → symbol T N
deriving DecidableEq

/-- Transformation rule for a grammar without any restrictions. -/
structure grule (T : Type) (N : Type) where
  input_L : List (symbol T N)
  input_N : N
  input_R : List (symbol T N)
  output_string : List (symbol T N)

/-- Grammar (unrestricted) that generates words over the alphabet `T` (a type of terminals). -/
structure grammar (T : Type) where
  nt : Type -- type of nonterminals
  initial : nt -- initial symbol
  rules : List (grule T nt) -- rewrite rules

variable {T : Type}

/-- One step of grammatical transformation. -/
def grammar_transforms (g : grammar T) (w₁ w₂ : List (symbol T g.nt)) : Prop :=
  ∃ r : grule T g.nt,
    r ∈ g.rules ∧
      ∃ u v : List (symbol T g.nt),
        (w₁ = u ++ r.input_L ++ [symbol.nonterminal r.input_N] ++ r.input_R ++ v) ∧
        (w₂ = u ++ r.output_string ++ v)

/-- Any number of steps of grammatical transformation; reflexive+transitive closure of `grammar_transforms`. -/
def grammar_derives (g : grammar T) :
    List (symbol T g.nt) → List (symbol T g.nt) → Prop :=
  Relation.ReflTransGen (grammar_transforms g)

/-- Accepts a word (a list of terminals) iff it can be derived from the initial nonterminal. -/
def grammar_generates (g : grammar T) (w : List T) : Prop :=
  grammar_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal w)

/-- The set of words that can be derived from the initial nonterminal. -/
def grammar_language (g : grammar T) : Language T :=
  SetOf (grammar_generates g)

/-- Predicate "is recursively-enumerable"; defined by existence of a grammar for the given language. -/
def is_RE (L : Language T) : Prop :=
  ∃ g : grammar T, grammar_language g = L
