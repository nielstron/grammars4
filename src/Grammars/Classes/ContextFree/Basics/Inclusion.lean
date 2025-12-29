import Grammars.Classes.ContextFree.Basics.Toolbox
import Grammars.Classes.ContextSensitive.Basics.Inclusion

variable {T : Type}


def csg_of_cfg (g : CF_grammar T) : CS_grammar T :=
CS_grammar.mk g.nt g.initial (List.map (fun r : g.nt × (List (symbol T g.nt)) =>
  csrule.mk [] r.fst [] r.snd) g.rules)

def grammar_of_cfg (g : CF_grammar T) : grammar T :=
grammar.mk g.nt g.initial (List.map (fun r : g.nt × (List (symbol T g.nt)) =>
  grule.mk [] r.fst [] r.snd) g.rules)

lemma grammar_of_cfg_well_defined (g : CF_grammar T) :
  grammar_of_csg (csg_of_cfg g) = grammar_of_cfg g :=
by
  cases g with
  | mk nt initial rules =>
    simp [grammar_of_csg, csg_of_cfg, grammar_of_cfg, List.map_map, List.append_nil]

lemma grammar_of_csg_of_cfg :
  grammar_of_csg ∘ csg_of_cfg = @grammar_of_cfg T :=
by
  funext g
  exact grammar_of_cfg_well_defined g

lemma CF_language_eq_CS_language (g : CF_grammar T) :
  CF_language g = CS_language (csg_of_cfg g) :=
by
  unfold CF_language
  unfold CS_language
  ext1 w
  change
    CF_derives g [symbol.nonterminal g.initial] (List.map symbol.terminal w) ↔
    CS_derives (csg_of_cfg g) [symbol.nonterminal (csg_of_cfg g).initial] (List.map symbol.terminal w)
  constructor
  ·
    have indu :
      ∀ v : List (symbol T g.nt),
        CF_derives g [symbol.nonterminal g.initial] v →
          CS_derives (csg_of_cfg g) [symbol.nonterminal (csg_of_cfg g).initial] v :=
    by
      intro v h
      induction h with
      | refl =>
        apply CS_deri_self
      | tail _ hyp ih =>
        apply CS_deri_of_deri_tran ih
        unfold CF_transforms at hyp
        unfold CS_transforms
        rcases hyp with ⟨r, u, w, rin, bef, aft⟩
        refine ⟨csrule.mk [] r.fst [] r.snd, u, w, ?_, ?_, ?_⟩
        ·
          simpa [csg_of_cfg, rin]
        ·
          simpa [List.append_nil] using bef
        ·
          simpa [List.append_nil] using aft
    exact indu (List.map symbol.terminal w)
  ·
    have indu :
      ∀ v : List (symbol T g.nt),
        CS_derives (csg_of_cfg g) [symbol.nonterminal g.initial] v →
          CF_derives g [symbol.nonterminal (csg_of_cfg g).initial] v :=
    by
      intro v h
      induction h with
      | refl =>
        apply CF_deri_self
      | tail _ hyp ih =>
        apply CF_deri_of_deri_tran ih
        unfold CS_transforms at hyp
        unfold CF_transforms
        rcases hyp with ⟨r, u, w, rin, bef, aft⟩
        rcases (List.mem_map.1 rin) with ⟨r₀, r₀_in, r_eq⟩
        cases r_eq
        refine ⟨(r₀.fst, r₀.snd), u, w, r₀_in, ?_, ?_⟩
        ·
          simpa [List.append_nil] using bef
        ·
          simpa [List.append_nil] using aft
    exact indu (List.map symbol.terminal w)

lemma CF_language_eq_grammar_language (g : CF_grammar T) :
  CF_language g = grammar_language (grammar_of_cfg g) :=
by
  rw [←grammar_of_cfg_well_defined]
  rw [CF_language_eq_CS_language]
  rw [CS_language_eq_grammar_language]

theorem CF_subclass_CS {L : Language T} :
  is_CF L → is_CS L :=
by
  rintro ⟨g, eq_L⟩
  use csg_of_cfg g
  rw [←eq_L]
  rw [CF_language_eq_CS_language]

theorem CF_subclass_RE {L : Language T} :
  is_CF L → is_RE L :=
CS_subclass_RE ∘ CF_subclass_CS
