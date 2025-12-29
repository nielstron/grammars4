import Grammars.Classes.ContextFree.Basics.Toolbox
import Grammars.Utilities.LanguageOperations
import Grammars.Utilities.ListUtils


open Grammars

variable {T : Type}

section auxiliary

private def reversal_grammar (g : CF_grammar T) : CF_grammar T :=
CF_grammar.mk g.nt g.initial (List.map (
    fun r : g.nt × List (symbol T g.nt) => (r.fst, List.reverse r.snd)
  ) g.rules)

private lemma map_reverse_reverse {nt : Type} (rules : List (nt × List (symbol T nt))) :
  List.map (fun r => (r.fst, r.snd.reverse.reverse)) rules = rules := by
  induction rules with
  | nil => rfl
  | cons h t ih =>
    cases h
    simp [List.reverse_reverse, ih]

private lemma map_reverse_reverse_comp {nt : Type} (rules : List (nt × List (symbol T nt))) :
  List.map ((fun r => (r.1, r.2.reverse)) ∘ fun r => (r.1, r.2.reverse)) rules = rules := by
  induction rules with
  | nil => rfl
  | cons h t ih =>
    cases h
    simp [Function.comp, List.reverse_reverse, ih]

private lemma dual_of_reversal_grammar (g : CF_grammar T) :
  reversal_grammar (reversal_grammar g) = g :=
by
  cases g with
  | mk nt initial rules =>
    simp [reversal_grammar, map_reverse_reverse_comp]

private lemma derives_reversed (g : CF_grammar T) (v : List (symbol T g.nt)) :
  CF_derives (reversal_grammar g) [symbol.nonterminal (reversal_grammar g).initial] v →
    CF_derives g [symbol.nonterminal g.initial] v.reverse :=
by
  intro hv
  induction hv with
  | refl =>
    rw [List.reverse_singleton]
    apply CF_deri_self
  | tail _ orig ih =>
    apply CF_deri_of_deri_tran ih
    rcases orig with ⟨r, x, y, rin, bef, aft⟩
    change r ∈ (List.map
      (fun r : g.nt × List (symbol T g.nt) => (r.fst, List.reverse r.snd)) g.rules) at rin
    rcases (List.mem_map.1 rin) with ⟨r₀, rin₀, r_from_r₀⟩
    refine ⟨r₀, y.reverse, x.reverse, rin₀, ?_, ?_⟩
    ·
      have fst_from_r : r₀.fst = r.fst := by
        rw [←r_from_r₀]
      have hrev := congr_arg List.reverse bef
      simpa [fst_from_r, List.reverse_append, List.reverse_reverse] using hrev
    ·
      have snd_from_r : r₀.snd = r.snd.reverse := by
        rw [←r_from_r₀]
        rw [List.reverse_reverse]
      have hrev := congr_arg List.reverse aft
      simpa [snd_from_r, List.reverse_append, List.reverse_reverse] using hrev

private lemma reversed_word_in_original_language {g : CF_grammar T} {w : List T}
    (hyp : w ∈ CF_language (reversal_grammar g)) :
  w.reverse ∈ CF_language g :=
by
  unfold CF_language at *
  rw [Set.mem_setOf_eq] at *
  unfold CF_generates at *
  unfold CF_generates_str at *
  rw [List.map_reverse]
  exact derives_reversed g (List.map symbol.terminal w) hyp

end auxiliary


/-- The class of context-free languages is closed under reversal. -/
theorem CF_of_reverse_CF (L : Language T) :
  is_CF L  →  is_CF (reverseLang L)  :=
by
  rintro ⟨g, hgL⟩
  rw [←hgL]

  use reversal_grammar g
  unfold reverseLang

  apply Set.eq_of_subset_of_subset
  ·
    intro w hwL
    change w.reverse ∈ CF_language g
    exact reversed_word_in_original_language hwL
  ·
    intro w hwL
    change w.reverse ∈ CF_language g at hwL

    have pre_reversal : ∃ g₀, g = reversal_grammar g₀
    {
      use reversal_grammar g
      rw [dual_of_reversal_grammar]
    }
    cases pre_reversal with
    | intro g₀ pre_rev =>
      rw [pre_rev] at hwL ⊢
      have finished_modulo_reverses := reversed_word_in_original_language hwL
      rw [dual_of_reversal_grammar]
      rw [List.reverse_reverse] at finished_modulo_reverses
      exact finished_modulo_reverses
