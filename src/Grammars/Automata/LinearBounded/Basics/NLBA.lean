import Mathlib
import Grammars.Automata.LinearBounded.Basics.LBA

/-!
# Nondeterministic Linear Bounded Automata

A **nondeterministic linear bounded automaton** (NLBA) is a nondeterministic Turing machine
whose read/write head is restricted to the portion of the tape containing the input.

We reuse the `LBA.BoundedTape` and `LBA.Cfg` infrastructure from the deterministic LBA
development.

## Main Definitions

* `NLBA.Machine Γ Λ` — A nondeterministic linearly bounded automaton
* `NLBA.Step` — Single nondeterministic computation step
* `NLBA.Reaches` — Multi-step reachability (reflexive-transitive closure of `Step`)
* `NLBA.Accepts` — Whether the machine accepts (can reach an accepting state)
* `NLBA.AcceptsList` — Acceptance for list-based inputs via an embedding
* `is_NLBA` — Predicate: a language is NLBA-recognizable

## References

* Kuroda, S.Y. (1964), "Classes of languages and linear-bounded automata"
* Myhill, J. (1960), "Linear bounded automata"
-/

namespace NLBA

/-! ### Machine Definition -/

/-- A nondeterministic linearly bounded automaton.
- `Γ` is the tape alphabet
- `Λ` is the finite set of states
- `transition` maps `(state, symbol)` to a *set* of possible `(new_state, write_symbol, direction)`
  triples, enabling nondeterminism.
- `accept` determines which states are accepting.
- `initial` is the start state. -/
structure Machine (Γ : Type*) (Λ : Type*) where
  /-- Nondeterministic transition relation. -/
  transition : Λ → Γ → Set (Λ × Γ × LBA.Dir)
  /-- Which states are accepting. -/
  accept : Λ → Bool
  /-- The initial state. -/
  initial : Λ

/-! ### Step and Reachability -/

/-- One step of nondeterministic computation: the machine reads the symbol under the head,
nondeterministically chooses a transition, writes a symbol, and moves the head. -/
def Step {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg cfg' : LBA.Cfg Γ Λ n) : Prop :=
  ∃ q' a d, (q', a, d) ∈ M.transition cfg.state cfg.tape.read ∧
    cfg' = ⟨q', (cfg.tape.write a).moveHead d⟩

/-- Multi-step reachability: the reflexive-transitive closure of `Step`. -/
def Reaches {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) : LBA.Cfg Γ Λ n → LBA.Cfg Γ Λ n → Prop :=
  Relation.ReflTransGen (Step M)

/-- The NLBA accepts from configuration `cfg` if there exists a computation path
that reaches a configuration with an accepting state. -/
def Accepts {Γ : Type*} {Λ : Type*} {n : ℕ}
    (M : Machine Γ Λ) (cfg : LBA.Cfg Γ Λ n) : Prop :=
  ∃ cfg' : LBA.Cfg Γ Λ n, Reaches M cfg cfg' ∧ M.accept cfg'.state = true

/-! ### Language Recognition for List-based Inputs -/

/-- Load a non-empty list onto a bounded tape. -/
noncomputable def loadList {Γ : Type*} (w : List Γ) (hw : w ≠ []) :
    LBA.BoundedTape Γ (w.length - 1) :=
  ⟨fun i => w.get ⟨i.val, by have := i.isLt; have := List.length_pos_of_ne_nil hw; omega⟩,
   ⟨0, by have := List.length_pos_of_ne_nil hw; omega⟩⟩

/-- Initial configuration for a non-empty list input. -/
noncomputable def initCfgList {Γ : Type*} {Λ : Type*}
    (M : Machine Γ Λ) (w : List Γ) (hw : w ≠ []) :
    LBA.Cfg Γ Λ (w.length - 1) :=
  ⟨M.initial, loadList w hw⟩

/-- The language recognized by an NLBA, defined on non-empty lists.
A non-empty word `w` is accepted if the NLBA can reach an accepting state starting
from the initial configuration with `w` on the tape.
The empty word is never accepted (the tape always has at least one cell). -/
noncomputable def LanguageOfMachine {Γ : Type*} {Λ : Type*}
    (M : Machine Γ Λ) : Language Γ :=
  fun w => ∃ (hw : w ≠ []), Accepts M (initCfgList M w hw)

/-- The language recognized by an NLBA with an embedding from input alphabet to tape alphabet.
A word `w` over alphabet `T` is accepted if the encoded word on the tape leads to acceptance. -/
noncomputable def LanguageViaEmbed {T Γ : Type*} {Λ : Type*}
    (M : Machine Γ Λ) (embed : T → Γ) : Language T :=
  fun w => ∃ (hw : w.map embed ≠ []),
    Accepts M (initCfgList M (w.map embed) hw)

end NLBA

/-- A language `L` over alphabet `T` is **NLBA-recognizable** if there exist:
- A tape alphabet `Γ` and state set `Λ` (both finite, decidable equality)
- An injection `embed : T ↪ Γ` encoding input symbols into tape symbols
- An NLBA machine `M` over `Γ` and `Λ`
such that `L` is exactly the set of words accepted by `M` (via the embedding). -/
def is_NLBA {T : Type} (L : Language T) : Prop :=
  ∃ (Γ Λ : Type) (_ : Fintype Γ) (_ : Fintype Λ)
    (_ : DecidableEq Γ) (_ : DecidableEq Λ)
    (embed : T ↪ Γ)
    (M : NLBA.Machine Γ Λ),
    NLBA.LanguageViaEmbed M embed = L
