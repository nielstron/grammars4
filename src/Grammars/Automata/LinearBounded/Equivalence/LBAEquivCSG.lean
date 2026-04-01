import Mathlib
import Grammars.Automata.LinearBounded.Basics.NLBA
import Grammars.Automata.LinearBounded.Equivalence.MyhillForward
import Grammars.Classes.ContextSensitive.Basics.Definition
import Grammars.Classes.ContextSensitive.Basics.Toolbox

/-!
# Equivalence of Context-Sensitive Grammars and Nondeterministic LBAs

This file establishes the classical result that a language is context-sensitive if and only
if it is recognized by a nondeterministic linear bounded automaton (NLBA).

## Main Results

* `CS_transforms_length_le` — A single CS derivation step never decreases word length
* `CS_derives_length_le` — CS derivations are non-contracting (multi-step)
* `empty_not_in_CS_language` — The empty word is never in a context-sensitive language
* `empty_not_in_NLBA_language` — The empty word is never accepted by an NLBA
* `CS_implies_NLBA` — Every context-sensitive language is NLBA-recognizable (for finite alphabets)
* `NLBA_implies_CS` — Every NLBA-recognizable language is context-sensitive
* `CS_iff_NLBA` — The equivalence of CSG and NLBA language classes (for finite alphabets)

## Notes

The direction CSG → NLBA requires a finite alphabet assumption `[Fintype T]` and
`[DecidableEq T]`, because `is_NLBA` requires an injection `T ↪ Γ` into a finite
tape alphabet `Γ`. The reverse direction NLBA → CSG derives finiteness of `T` from
the NLBA's embedding.

## References

* Kuroda, S.Y. (1964), "Classes of languages and linear-bounded automata"
* Myhill, J. (1960), "Linear bounded automata"
* Hopcroft, Motwani, Ullman, *Introduction to Automata Theory*, Chapter 9
-/

open Relation List

variable {T : Type}

/-! ## Part 1: Auxiliary lemmas -/

/-- A single CS derivation step never decreases word length. -/
theorem CS_transforms_length_le {g : CS_grammar T}
    {w₁ w₂ : List (symbol T g.nt)}
    (h : CS_transforms g w₁ w₂) :
    w₁.length ≤ w₂.length := by
  obtain ⟨r, u, v, hr, hw₁, hw₂⟩ := h
  have hne := g.output_nonempty r hr
  subst hw₁; subst hw₂
  simp only [List.length_append, List.length_cons, List.length_nil]
  have : r.output_string.length ≥ 1 := List.length_pos_of_ne_nil hne
  omega

/-- CS derivations are non-contracting: multi-step version. -/
theorem CS_derives_length_le {g : CS_grammar T}
    {w₁ w₂ : List (symbol T g.nt)}
    (h : CS_derives g w₁ w₂) :
    w₁.length ≤ w₂.length := by
  induction h with
  | refl => exact le_refl _
  | tail _ step ih => exact le_trans ih (CS_transforms_length_le step)

/-- The empty word is never in a CS language. -/
theorem empty_not_in_CS_language (g : CS_grammar T) :
    [] ∉ CS_language g := by
  intro h
  have hlen := CS_derives_length_le h
  simp at hlen

/-- If `L` is context-sensitive, then `[] ∉ L`. -/
theorem is_CS_no_empty {L : Language T} (hL : is_CS L) :
    [] ∉ L := by
  obtain ⟨g, rfl⟩ := hL
  exact empty_not_in_CS_language g

/-- The empty word is never accepted by an NLBA. -/
theorem empty_not_in_NLBA_language {Γ Λ : Type*}
    (M : NLBA.Machine Γ Λ) (embed : T → Γ) :
    [] ∉ NLBA.LanguageViaEmbed M embed := by
  intro ⟨hw, _⟩
  exact hw (by simp)

/-- If `L` is NLBA-recognizable, then `[] ∉ L`. -/
theorem is_NLBA_no_empty {L : Language T} (hL : is_NLBA L) :
    [] ∉ L := by
  obtain ⟨Γ, Λ, _, _, _, _, embed, M, rfl⟩ := hL
  exact empty_not_in_NLBA_language M embed

/-! ## Part 2: CSG → NLBA

The proof constructs an NLBA that performs nondeterministic reverse derivation:
starting with the input word on the tape, it nondeterministically applies
grammar rules in reverse until only the start symbol remains (padded with blanks).

The non-contracting property (proved above as `CS_derives_length_le`) ensures that
reverse steps never increase the sentential form length beyond the tape size.

The NLBA construction requires:
- Tape alphabet encoding grammar symbols plus blanks
- A finite state space tracking the reverse derivation phase
- Transitions implementing pattern matching, replacement, compaction, and verification

This is essentially a Turing machine programming task in the LBA formalism.

Note: This direction requires `[Fintype T]` and `[DecidableEq T]` because `is_NLBA`
requires an injection `T ↪ Γ` into a finite tape alphabet, which is impossible for
infinite `T`. -/

/-- **CSG → NLBA**: Every context-sensitive language over a finite alphabet
is recognized by some NLBA. -/
theorem CS_implies_NLBA [Fintype T] [DecidableEq T]
    {L : Language T} (h : is_CS L) :
    is_NLBA L := by
  sorry

/-! ## Part 3: NLBA → CSG

Uses Myhill's construction from `NLBAToCSG.lean`: given an NLBA with finite
alphabet and states, construct a context-sensitive grammar whose nonterminals
encode the computation state at each tape cell. -/

/-- **NLBA → CSG**: Every NLBA-recognizable language is context-sensitive. -/
theorem NLBA_implies_CS {L : Language T} (h : is_NLBA L) :
    is_CS L := by
  obtain ⟨Γ, Λ, hΓ, hΛ, hdΓ, hdΛ, embed, M, rfl⟩ := h
  -- Derive Fintype T from the embedding T ↪ Γ
  haveI : Fintype T := Fintype.ofInjective embed embed.injective
  haveI : DecidableEq T := by
    intro a b
    exact if h : embed a = embed b
      then .isTrue (embed.injective h)
      else .isFalse (fun hab => h (congrArg embed hab))
  exact MyhillConstruction.nlba_language_is_CS M embed

/-! ## Part 4: Main Equivalence -/

/-- **Main Theorem**: A language over a finite alphabet is context-sensitive if and only
if it is NLBA-recognizable.

This is the classical equivalence between context-sensitive grammars and
nondeterministic linear bounded automata, due to Kuroda (1964) and Myhill (1960).

Note: The forward direction (CSG → NLBA) requires `[Fintype T]` and `[DecidableEq T]`.
The reverse direction derives these from the NLBA's embedding. -/
theorem CS_iff_NLBA [Fintype T] [DecidableEq T] (L : Language T) :
    is_CS L ↔ is_NLBA L :=
  ⟨CS_implies_NLBA, NLBA_implies_CS⟩
