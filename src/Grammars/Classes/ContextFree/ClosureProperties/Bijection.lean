import Grammars.Classes.ContextFree.Basics.Toolbox
import Grammars.Utilities.LanguageOperations


open Grammars

variable {T₁ T₂ N : Type}

private def sT₂_of_sT₁ (π : T₁ ≃ T₂) : (symbol T₁ N) → (symbol T₂ N)
| (symbol.terminal t) => symbol.terminal (π t)
| (symbol.nonterminal n) => symbol.nonterminal n

private def sT₁_of_sT₂ (π : T₁ ≃ T₂) : (symbol T₂ N) → (symbol T₁ N)
| (symbol.terminal t) => symbol.terminal (π.symm t)
| (symbol.nonterminal n) => symbol.nonterminal n

private def lsT₂_of_lsT₁ (π : T₁ ≃ T₂) : List (symbol T₁ N) → List (symbol T₂ N) :=
List.map (sT₂_of_sT₁ π)

private def lsT₁_of_lsT₂ (π : T₁ ≃ T₂) : List (symbol T₂ N) → List (symbol T₁ N) :=
List.map (sT₁_of_sT₂ π)

@[simp] private lemma sT₁_of_sT₂_of_sT₁ (π : T₁ ≃ T₂) :
  ∀ s : symbol T₁ N, sT₁_of_sT₂ π (sT₂_of_sT₁ π s) = s := by
  intro s
  cases s <;> simp [sT₁_of_sT₂, sT₂_of_sT₁]

@[simp] private lemma sT₂_of_sT₁_of_sT₂ (π : T₁ ≃ T₂) :
  ∀ s : symbol T₂ N, sT₂_of_sT₁ π (sT₁_of_sT₂ π s) = s := by
  intro s
  cases s <;> simp [sT₁_of_sT₂, sT₂_of_sT₁]

private lemma lsT₁_of_lsT₂_of_lsT₁ (π : T₁ ≃ T₂) :
  ∀ s : List (symbol T₁ N), lsT₁_of_lsT₂ π (lsT₂_of_lsT₁ π s) = s := by
  intro s
  induction s with
  | nil => rfl
  | cons h t ih =>
    simpa [lsT₁_of_lsT₂, lsT₂_of_lsT₁, List.map_map] using ih

private lemma lsT₂_of_lsT₁_of_lsT₂ (π : T₁ ≃ T₂) :
  ∀ s : List (symbol T₂ N), lsT₂_of_lsT₁ π (lsT₁_of_lsT₂ π s) = s := by
  intro s
  induction s with
  | nil => rfl
  | cons h t ih =>
    simpa [lsT₁_of_lsT₂, lsT₂_of_lsT₁, List.map_map] using ih

private lemma map_terminal_symm (π : T₁ ≃ T₂) (w : List T₂) :
  List.map (sT₂_of_sT₁ (N := N) π ∘ symbol.terminal (N := N) ∘ π.symm) w =
    List.map (symbol.terminal (N := N)) w := by
  induction w with
  | nil => rfl
  | cons h t ih =>
    simp [Function.comp, sT₂_of_sT₁, ih]

/-- The class of context-free languages is closed under bijection between terminal alphabets. -/
theorem CF_of_bijemap_CF (π : T₁ ≃ T₂) (L : Language T₁) :
  is_CF L  →  is_CF (bijemapLang L π)  :=
by
  rintro ⟨g, hg⟩

  let g' : CF_grammar T₂ := CF_grammar.mk g.nt g.initial (List.map
      (fun r : g.nt × (List (symbol T₁ g.nt)) => (r.fst, lsT₂_of_lsT₁ π r.snd))
    g.rules)
  use g'

  apply Set.eq_of_subset_of_subset
  ·
    intro w hw
    unfold bijemapLang
    change List.map π.symm w ∈ L
    rw [←hg]

    unfold CF_language at hw ⊢
    rw [Set.mem_setOf_eq] at hw ⊢
    unfold CF_generates at hw ⊢
    unfold CF_generates_str at hw ⊢

    have deri_of_deri :
      ∀ v : List (symbol T₂ g'.nt),
        CF_derives g' [symbol.nonterminal g'.initial] v →
          CF_derives g [symbol.nonterminal g.initial] (lsT₁_of_lsT₂ π v) :=
    by
      intros v hv
      induction hv with
      | refl =>
        apply CF_deri_self
      | tail _ step ih =>
        apply CF_deri_of_deri_tran
        · exact ih
        rcases step with ⟨r, x, y, r_in, bef, aft⟩
        let r₁ := (r.fst, lsT₁_of_lsT₂ π r.snd)
        let x₁ := lsT₁_of_lsT₂ π x
        let y₁ := lsT₁_of_lsT₂ π y
        use r₁
        use x₁
        use y₁
        constructor
        ·
          change (r.fst, lsT₁_of_lsT₂ π r.snd) ∈ g.rules
          rcases (List.mem_map.1 r_in) with ⟨r', r'_in, r'_eq⟩
          rcases r' with ⟨a, b⟩
          cases r'_eq
          simpa [lsT₁_of_lsT₂_of_lsT₁] using r'_in
        ·
          constructor
          ·
            simp [bef, lsT₁_of_lsT₂, List.map_append, x₁, y₁, r₁, sT₁_of_sT₂]
          ·
            simp [aft, lsT₁_of_lsT₂, List.map_append, x₁, y₁, r₁, sT₁_of_sT₂]
    specialize deri_of_deri (List.map symbol.terminal w) hw
    unfold lsT₁_of_lsT₂ at deri_of_deri
    rw [List.map_map] at *
    convert deri_of_deri
  ·
    intro w hw
    unfold bijemapLang at hw
    change List.map π.symm w ∈ L at hw
    rw [←hg] at hw
    unfold CF_language at hw
    rw [Set.mem_setOf_eq] at hw
    unfold CF_generates at hw
    rw [List.map_map] at hw
    unfold CF_generates_str at hw

    unfold CF_language
    change CF_generates_str g' (List.map symbol.terminal w)
    unfold CF_generates_str

    have deri_of_deri :
      ∀ v : List (symbol T₁ g.nt),
        CF_derives g [symbol.nonterminal g.initial] v →
          CF_derives g' [symbol.nonterminal g'.initial] (lsT₂_of_lsT₁ π v) :=
    by
      intros v hv
      induction hv with
      | refl =>
        apply CF_deri_self
      | tail _ step ih =>
        apply CF_deri_of_deri_tran
        · exact ih
        rcases step with ⟨r, x, y, r_in, bef, aft⟩
        let r₂ := (r.fst, lsT₂_of_lsT₁ π r.snd)
        let x₂ := lsT₂_of_lsT₁ π x
        let y₂ := lsT₂_of_lsT₁ π y
        use r₂
        use x₂
        use y₂
        constructor
        ·
          rw [List.mem_map]
          refine ⟨r, r_in, ?_⟩
          rfl
        ·
          constructor
          ·
            simp [bef, lsT₂_of_lsT₁, List.map_append, x₂, y₂, r₂, sT₂_of_sT₁]
          ·
            simp [aft, lsT₂_of_lsT₁, List.map_append, x₂, y₂, r₂, sT₂_of_sT₁]
    specialize deri_of_deri (List.map (symbol.terminal ∘ π.symm) w) hw
    rw [lsT₂_of_lsT₁, List.map_map] at deri_of_deri
    simpa [map_terminal_symm] using deri_of_deri
  
