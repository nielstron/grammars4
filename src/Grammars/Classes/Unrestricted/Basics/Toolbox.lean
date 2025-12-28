import Grammars.Classes.Unrestricted.Basics.Definition

open Relation

variable {T : Type} {g : grammar T}


/-- The Relation `grammar_derives` is reflexive. -/
lemma grammar_deri_self {w : List (symbol T g.nt)} :
  grammar_derives g w w :=
ReflTransGen.refl

lemma grammar_deri_of_tran {v w : List (symbol T g.nt)} :
  grammar_transforms g v w → grammar_derives g v w :=
ReflTransGen.single

/-- The Relation `grammar_derives` is transitive. -/
lemma grammar_deri_of_deri_deri {u v w : List (symbol T g.nt)}
    (huv : grammar_derives g u v) (hvw : grammar_derives g v w) :
  grammar_derives g u w :=
ReflTransGen.trans huv hvw

lemma grammar_deri_of_deri_tran {u v w : List (symbol T g.nt)}
    (huv : grammar_derives g u v) (hvw : grammar_transforms g v w) :
  grammar_derives g u w :=
grammar_deri_of_deri_deri huv (grammar_deri_of_tran hvw)

lemma grammar_deri_of_tran_deri {u v w : List (symbol T g.nt)}
    (huv : grammar_transforms g u v) (hvw : grammar_derives g v w) :
  grammar_derives g u w :=
grammar_deri_of_deri_deri (grammar_deri_of_tran huv) hvw

lemma grammar_tran_or_id_of_deri {u w : List (symbol T g.nt)} (ass : grammar_derives g u w) :
  (u = w) ∨
  (∃ v : List (symbol T g.nt), (grammar_transforms g u v) ∧ (grammar_derives g v w)) :=
ReflTransGen.cases_head ass


lemma grammar_deri_with_prefix {w₁ w₂ : List (symbol T g.nt)}
    (pᵣ : List (symbol T g.nt))
    (ass : grammar_derives g w₁ w₂) :
  grammar_derives g (pᵣ ++ w₁) (pᵣ ++ w₂) :=
by
  induction ass with
  | refl =>
      simpa using grammar_deri_self (g := g) (w := pᵣ ++ w₁)
  | tail ass step ih =>
      refine grammar_deri_of_deri_tran ih ?_
      rcases step with ⟨r, rin, u, v, hbef, haft⟩
      refine ⟨r, rin, pᵣ ++ u, v, ?_, ?_⟩
      · simp [hbef, List.append_assoc]
      · simp [haft, List.append_assoc]

lemma grammar_deri_with_postfix {w₁ w₂ : List (symbol T g.nt)}
    (pₒ : List (symbol T g.nt))
    (ass : grammar_derives g w₁ w₂) :
  grammar_derives g (w₁ ++ pₒ) (w₂ ++ pₒ) :=
by
  induction ass with
  | refl =>
      simpa using grammar_deri_self (g := g) (w := w₁ ++ pₒ)
  | tail ass step ih =>
      refine grammar_deri_of_deri_tran ih ?_
      rcases step with ⟨r, rin, u, v, hbef, haft⟩
      refine ⟨r, rin, u, v ++ pₒ, ?_, ?_⟩
      · simp [hbef, List.append_assoc]
      · simp [haft, List.append_assoc]


def as_terminal {N : Type} : symbol T N → Option T
| (symbol.terminal t)    => some t
| (symbol.nonterminal _) => none

def all_used_terminals (g : grammar T) : List T :=
List.filterMap as_terminal (List.flatten (List.map grule.output_string g.rules))
