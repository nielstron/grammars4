import Grammars.Classes.ContextSensitive.Basics.Inclusion
import Grammars.Classes.Unrestricted.ClosureProperties.Concatenation

variables {T : Type}


private def wrap_CS_rule₁ {N₁ : Type} (N₂ : Type) (r : csrule T N₁) :
  csrule T (nnn T N₁ N₂) :=
csrule.mk
  (List.map (wrap_symbol₁ N₂) r.context_left)
  (Sum.inl (some (Sum.inl r.input_nonterminal)))
  (List.map (wrap_symbol₁ N₂) r.context_right)
  (List.map (wrap_symbol₁ N₂) r.output_string)

private def wrap_CS_rule₂ {N₂ : Type} (N₁ : Type) (r : csrule T N₂) :
  csrule T (nnn T N₁ N₂) :=
csrule.mk
  (List.map (wrap_symbol₂ N₁) r.context_left)
  (Sum.inl (some (Sum.inr r.input_nonterminal)))
  (List.map (wrap_symbol₂ N₁) r.context_right)
  (List.map (wrap_symbol₂ N₁) r.output_string)

private def CS_rules_for_terminals₁ (N₂ : Type) (g : CS_grammar T) :
  List (csrule T (nnn T g.nt N₂)) :=
List.map (λ t, csrule.mk [] (Sum.inr (Sum.inl t)) [] [symbol.terminal t])
  (all_used_terminals (grammar_of_csg g))

private def CS_rules_for_terminals₂ (N₁ : Type) (g : CS_grammar T) :
  List (csrule T (nnn T N₁ g.nt)) :=
List.map (λ t, csrule.mk [] (Sum.inr (Sum.inr t)) [] [symbol.terminal t])
  (all_used_terminals (grammar_of_csg g))

private def big_CS_grammar (g₁ g₂ : CS_grammar T) : CS_grammar T :=
CS_grammar.mk
  (nnn T g₁.nt g₂.nt)
  (Sum.inl none)
  ((csrule.mk [] (Sum.inl none) [] [
    symbol.nonterminal (Sum.inl (some (Sum.inl g₁.initial))),
    symbol.nonterminal (Sum.inl (some (Sum.inr g₂.initial)))]
  ) :: (
    (List.map (wrap_CS_rule₁ g₂.nt) g₁.rules ++ List.map (wrap_CS_rule₂ g₁.nt) g₂.rules) ++
    (CS_rules_for_terminals₁ g₂.nt g₁ ++ CS_rules_for_terminals₂ g₁.nt g₂)
  ))

private lemma big_CS_grammar_same_language (g₁ g₂ : CS_grammar T) :
  CS_language (big_CS_grammar g₁ g₂) = grammar_language (big_grammar (grammar_of_csg g₁) (grammar_of_csg g₂)) :=
by
  rw CS_language_eq_grammar_language,
  congr,
  unfold big_CS_grammar,
  unfold grammar_of_csg,
  unfold big_grammar,
  dsimp only [List.map],
  congr,
  repeat {
    rw List.map_append,
  },
  apply congr_arg2,
  {
    apply congr_arg2;
    {
      rw List.map_map,
      rw List.map_map,
      apply congr_arg2,
      {
        ext,
        cases x,
        change _ = grule.mk _ _ _ _,
        finish,
      },
      refl,
    },
  },
  {
    apply congr_arg2,
    {
      unfold rules_for_terminals₁,
      unfold CS_rules_for_terminals₁,
      rw List.map_map,
      unfold grammar_of_csg,
      finish,
    },
    {
      unfold rules_for_terminals₂,
      unfold CS_rules_for_terminals₂,
      rw List.map_map,
      unfold grammar_of_csg,
      finish,
    },
  },


private theorem bonus_CS_of_CS_c_CS (L₁ : Language T) (L₂ : Language T) :
  is_CS L₁  ∧  is_CS L₂   →   is_CS (L₁ * L₂)   :=
by
  rintro ⟨⟨g₁, eq_L₁⟩, ⟨g₂, eq_L₂⟩⟩,
  rw CS_language_eq_grammar_language g₁ at eq_L₁,
  rw CS_language_eq_grammar_language g₂ at eq_L₂,

  use big_CS_grammar g₁ g₂,
  rw big_CS_grammar_same_language,

  apply Set.eq_of_subSetOf_subset,
  {
    intros w hyp,
    rw ←eq_L₁,
    rw ←eq_L₂,
    exact in_concatenated_of_in_big hyp,
  },
  {
    intros w hyp,
    rw ←eq_L₁ at hyp,
    rw ←eq_L₂ at hyp,
    exact in_big_of_in_concatenated hyp,
  }
