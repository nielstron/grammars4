import Grammars.Classes.ContextSensitive.Basics.Definition

variables {T : Type} {g : CS_grammar T}


/-- The Relation `CS_derives` is reflexive. -/
lemma CS_deri_self {w : List (symbol T g.nt)} :
  CS_derives g w w :=
Relation.refl_trans_gen.refl

lemma CS_deri_of_tran {v w : List (symbol T g.nt)} :
  CS_transforms g v w → CS_derives g v w :=
Relation.refl_trans_gen.single

/-- The Relation `CS_derives` is transitive. -/
lemma CS_deri_of_deri_deri {u v w : List (symbol T g.nt)}
    (huv : CS_derives g u v) (hvw : CS_derives g v w) :
  CS_derives g u w :=
Relation.refl_trans_gen.trans huv hvw

lemma CS_deri_of_deri_tran {u v w : List (symbol T g.nt)}
    (huv : CS_derives g u v) (hvw : CS_transforms g v w) :
  CS_derives g u w :=
CS_deri_of_deri_deri huv (CS_deri_of_tran hvw)

lemma CS_deri_of_tran_deri {u v w : List (symbol T g.nt)}
    (huv : CS_transforms g u v) (hvw : CS_derives g v w) :
  CS_derives g u w :=
CS_deri_of_deri_deri (CS_deri_of_tran huv) hvw

lemma CS_tran_or_id_of_deri {u w : List (symbol T g.nt)} (ass : CS_derives g u w) :
  (u = w) ∨
  (∃ v : List (symbol T g.nt), (CS_transforms g u v) ∧ (CS_derives g v w)) :=
Relation.refl_trans_gen.cases_head ass
