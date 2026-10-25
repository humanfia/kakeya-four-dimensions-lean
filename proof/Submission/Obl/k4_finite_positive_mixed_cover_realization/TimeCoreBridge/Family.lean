-- Adapted from this LOT tree, o210, session x0795, commit f6d85510,
-- Submission/Obl/k4_clean_cover_graph_atlas/Family.lean. Earlier provenance is retained below.
-- The path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree o194, session x0672, commit 69d09a7b8755,
-- Submission/Obl/k4_greedy_cover_graph_atlas/Family.lean. Earlier attributions follow.

-- Adapted from this LOT tree, o173, session x0598, commit 6ded8016fe11,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/Family.lean.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.Interface

/-!
# Assembling the preliminary improved atlas from a finite labelled family

`preImprovementAt_of_family`: any finite type of labels carrying charts, a list rule at the
terminal observation and the list-success mass floor gives the frozen `preImprovementAt`;
the `Fin` indexing is built here.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory

theorem preImprovementAt_of_family {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))} {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {B : Fin W → ℝ} {κ₁ Δ : ℝ} {m : ℕ} {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ} {M D : ℕ}
    {ε : ℝ} {ι : Type*} [Fintype ι] (r₂ : ℝ) (T₂ : ℕ) (γ₂ : ι → Fin W)
    (j₂ : ι → Fin (2 ^ T₂)) (c₂ u₂ : ι → EuclideanSpace ℝ (Fin 2))
    (Q₂ : ι → Matrix (Fin 2) (Fin 2) ℝ) (R₂ : ι → MvPolynomial (Fin 4) ℝ)
    (A₂ : ι → Set (ℕ × (Fin 6 → ℝ))) (F₂ : ι → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (lst : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset ι)
    (hdepth : r₂ + Δ * L ≤ L)
    (himp : (Δ * L ≤ r₂ ∧ (2 : ℝ) ^ T₂ ≤ Nk ^ (κ₁ * Δ * L / 2)) ∨
      ∃ i, i < m ∧ r i + Δ * L ≤ r₂ ∧ (2 : ℝ) ^ T₂ ≤ (2 : ℝ) ^ T i * Nk ^ (κ₁ * Δ * L / 2))
    (hcard : (Fintype.card ι : ℝ) ≤ Nk ^ M)
    (hdisj : ∀ b b', b ≠ b' → γ₂ b = γ₂ b' → j₂ b = j₂ b' → Disjoint (A₂ b) (A₂ b'))
    (hlst : ∀ w o, ((lst w o).card : ℝ) ≤ Nk ^ ε)
    (hlstm : ∀ w b, MeasurableSet {o | b ∈ lst w o})
    (hchart : ∀ b, chart Nk M D (Nk ^ ε) T₂ ((j₂ b : ℕ) : ℝ) r₂ (B (γ₂ b)) (E (γ₂ b))
      (c₂ b) (u₂ b) (Q₂ b) (R₂ b) (A₂ b) (F₂ b) True)
    (hmass : ENNReal.ofReal (Nk ^ (-ε)) ≤ ∑ b, ENNReal.ofReal (ω (γ₂ b)) *
      ((ν (γ₂ b)).prod volume) {p | p ∈ F₂ b ∧ b ∈ lst (γ₂ b) (obs (B (γ₂ b)) (δ Nk L) p)}) :
    preImprovementAt Nk L W ω ν E B κ₁ Δ m r T nw M D ε := by
  classical
  set e := Fintype.equivFin ι
  let lst' : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin (Fintype.card ι)) :=
    fun w o => (lst w o).map e.toEmbedding
  refine ⟨r₂, T₂, Fintype.card ι, γ₂ ∘ e.symm, j₂ ∘ e.symm, c₂ ∘ e.symm, u₂ ∘ e.symm,
    Q₂ ∘ e.symm, R₂ ∘ e.symm, A₂ ∘ e.symm, F₂ ∘ e.symm, lst', hdepth, himp, hcard, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro b b' hbb' hγ hj
    exact hdisj (e.symm b) (e.symm b') (fun h => hbb' (e.symm.injective h)) hγ hj
  · intro w o
    simp only [lst', Finset.card_map]
    exact hlst w o
  · intro w b
    have : {o | b ∈ lst' w o} = {o | e.symm b ∈ lst w o} := by
      ext o
      simp only [lst', Set.mem_ofPred_eq, Finset.mem_map_equiv]
    rw [this]
    exact hlstm w (e.symm b)
  · intro b
    exact hchart (e.symm b)
  · calc ENNReal.ofReal (Nk ^ (-ε)) ≤ _ := hmass
      _ = ∑ b, ENNReal.ofReal (ω ((γ₂ ∘ e.symm) b)) * ((ν ((γ₂ ∘ e.symm) b)).prod volume)
            {p | p ∈ (F₂ ∘ e.symm) b ∧ b ∈ lst' ((γ₂ ∘ e.symm) b)
              (obs (B ((γ₂ ∘ e.symm) b)) (δ Nk L) p)} := by
          refine (Fintype.sum_equiv e.symm _ _ (fun b => ?_)).symm
          simp only [Function.comp_apply, lst', Finset.mem_map_equiv]

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
