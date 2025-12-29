import Grammars.Classes.ContextSensitive.Basics.Toolbox
import Grammars.Classes.Unrestricted.Basics.Toolbox

variable {T : Type}


def grammar_of_csg (g : CS_grammar T) : grammar T :=
grammar.mk g.nt g.initial (List.map 
  (fun r : csrule T g.nt => grule.mk
    r.context_left r.input_nonterminal r.context_right
    (r.context_left ++ r.output_string ++ r.context_right)
  ) g.rules)

lemma CS_language_eq_grammar_language (g : CS_grammar T) :
  CS_language g = grammar_language (grammar_of_csg g) :=
by
  unfold CS_language
  unfold grammar_language
  ext1 w
  rw [Set.mem_setOf_eq]
  constructor
  ·
    have indu :
      ∀ v : List (symbol T g.nt),
        CS_derives g [symbol.nonterminal g.initial] v →
          grammar_derives (grammar_of_csg g) [symbol.nonterminal (grammar_of_csg g).initial] v :=
    by
      clear w
      intros v hypo
      induction hypo with
      | refl =>
        apply grammar_deri_self
      | tail _ step ih =>
        apply grammar_deri_of_deri_tran
        · exact ih
        unfold CS_transforms at step
        unfold grammar_transforms
        delta grammar_of_csg
        dsimp only
        rcases step with ⟨r, u, w, rin, bef, aft⟩
        use grule.mk
          r.context_left r.input_nonterminal r.context_right
          (r.context_left ++ r.output_string ++ r.context_right)
        constructor
        ·
          rw [List.mem_map]
          refine ⟨r, rin, ?_⟩
          rfl
        ·
          use u
          use w
          constructor
          · exact bef
          · simpa [List.append_assoc] using aft
    exact indu (List.map symbol.terminal w)
  ·
    have indu :
      ∀ v : List (symbol T g.nt),
        grammar_derives (grammar_of_csg g) [symbol.nonterminal (grammar_of_csg g).initial] v →
          CS_derives g [symbol.nonterminal g.initial] v :=
    by
      clear w
      intros v hypo
      induction hypo with
      | refl =>
        apply CS_deri_self
      | tail _ step ih =>
        apply CS_deri_of_deri_tran
        · exact ih
        unfold grammar_transforms at step
        unfold CS_transforms
        delta grammar_of_csg at step
        dsimp only at step
        rcases step with ⟨r, rin, u, w, bef, aft⟩
        rcases (List.mem_map.1 rin) with ⟨r', new_rule_in, new_rule_def⟩
        use r'
        use u
        use w
        constructor
        · exact new_rule_in
        ·
          constructor
          ·
            rw [←new_rule_def] at bef
            exact bef
          ·
            rw [←new_rule_def] at aft
            simpa [List.append_assoc] using aft
    exact indu (List.map symbol.terminal w)
  
  

theorem CS_subclass_RE {L : Language T} :
  is_CS L → is_RE L :=
by
  rintro ⟨g, eq_L⟩
  use grammar_of_csg g
  rw [←eq_L]
  rw [CS_language_eq_grammar_language]
