import Grammars.Classes.ContextFree.Basics.Definition

variables {T : Type} {g : CF_grammar T}


lemma CF_deri_of_tran {v w : List (symbol T g.nt)} :
  CF_transforms g v w → CF_derives g v w :=
Relation.ReflTransGen.single

/-- The Relation `CF_derives` is reflexive. -/
lemma CF_deri_self {w : List (symbol T g.nt)} :
  CF_derives g w w :=
Relation.ReflTransGen.refl

/-- The Relation `CF_derives` is transitive. -/
lemma CF_deri_of_deri_deri {u v w : List (symbol T g.nt)}
    (huv : CF_derives g u v)
    (hvw : CF_derives g v w) :
  CF_derives g u w :=
Relation.ReflTransGen.trans huv hvw

lemma CF_deri_of_deri_tran {u v w : List (symbol T g.nt)}
    (huv : CF_derives g u v)
    (hvw : CF_transforms g v w) :
  CF_derives g u w :=
CF_deri_of_deri_deri huv (CF_deri_of_tran hvw)

lemma CF_deri_of_tran_deri {u v w : List (symbol T g.nt)}
    (huv : CF_transforms g u v)
    (hvw : CF_derives g v w) :
  CF_derives g u w :=
CF_deri_of_deri_deri (CF_deri_of_tran huv) hvw

lemma CF_tran_or_id_of_deri {u w : List (symbol T g.nt)} (ass : CF_derives g u w) :
  (u = w) ∨
  (∃ v : List (symbol T g.nt), (CF_transforms g u v) ∧ (CF_derives g v w)) :=
Relation.ReflTransGen.cases_head ass

lemma CF_deri_with_prefix {w₁ w₂ : List (symbol T g.nt)}
    (pᵣ : List (symbol T g.nt))
    (ass : CF_derives g w₁ w₂) :
  CF_derives g (pᵣ ++ w₁) (pᵣ ++ w₂) := by
  -- CF_derives is a ReflTransGen, so its constructors are `refl` and `tail`.
  induction ass with
  | refl =>
      -- goal: CF_derives g (pᵣ ++ w₁) (pᵣ ++ w₁)
      -- use the “self-derivation” lemma and rewrite
      simpa using (CF_deri_self (g := g) (w := pᵣ ++ w₁))

  | tail ass' step ih =>
      -- Here we have:
      -- ass' : CF_derives g w₁ b✝
      -- step : CF_transforms g b✝ c✝
      -- ih   : CF_derives g (pᵣ ++ w₁) (pᵣ ++ b✝)
      --
      -- We want: CF_derives g (pᵣ ++ w₁) (pᵣ ++ c✝)
      apply CF_deri_of_deri_tran
      · exact ih
      ·
        -- unpack the last transformation step
        rcases step with ⟨r, r_in, v, w, h_bef, h_aft⟩
        refine ⟨r, r_in, pᵣ ++ v, w, ?_, ?_⟩
        · -- before rewriting
          -- (pᵣ ++ b✝) = (pᵣ ++ v) ++ ... ++ w
          simpa [h_bef, List.append_assoc]
        · -- after rewriting
          simpa [h_aft, List.append_assoc]

lemma CF_deri_with_prefix {w₁ w₂ : List (symbol T g.nt)}
    (pᵣ : List (symbol T g.nt))
    (ass : CF_derives g w₁ w₂) :
  CF_derives g (pᵣ ++ w₁) (pᵣ ++ w₂) :=
begin
  induction ass with a b irr hyp ih,
  {
    apply CF_deri_self,
  },
  apply CF_deri_of_deri_tran,
  {
    exact ih,
  },
  rcases hyp with ⟨r, r_in, v, w, h_bef, h_aft⟩,
  use r,
  split,
  {
    exact r_in,
  },
  use pᵣ ++ v,
  use w,
  rw h_bef,
  rw h_aft,
  split;
  simp only [List.append_assoc],
end

lemma CF_deri_with_postfix {w₁ w₂ : List (symbol T g.nt)}
    (pₒ : List (symbol T g.nt))
    (ass : CF_derives g w₁ w₂) :
  CF_derives g (w₁ ++ pₒ) (w₂ ++ pₒ) :=
begin
  induction ass with a b irr hyp ih,
  {
    apply CF_deri_self,
  },
  apply CF_deri_of_deri_tran,
  {
    exact ih,
  },
  rcases hyp with ⟨r, r_in, v, w, h_bef, h_aft⟩,
  use r,
  split,
  {
    exact r_in,
  },
  use v,
  use w ++ pₒ,
  rw h_bef,
  rw h_aft,
  split;
  simp only [List.append_assoc],
end

lemma CF_deri_with_prefix_and_postfix {w₁ w₂ : List (symbol T g.nt)}
    (pᵣ pₒ : List (symbol T g.nt))
    (ass : CF_derives g w₁ w₂) :
  CF_derives g (pᵣ ++ w₁ ++ pₒ) (pᵣ ++ w₂ ++ pₒ) :=
begin
  apply CF_deri_with_postfix,
  apply CF_deri_with_prefix,
  exact ass,
end
