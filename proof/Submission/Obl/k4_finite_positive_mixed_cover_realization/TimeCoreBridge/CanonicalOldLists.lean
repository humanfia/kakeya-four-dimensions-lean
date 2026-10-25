-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/CanonicalOldLists.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/CanonicalOldLists.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.Interface
import Submission.Obl.k4_remainder_pure_profile_normalization.ObservationImages
import Submission.Lib.K4XInterface.Formats

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open Set MeasureTheory Finset

/-- The old charts geometrically met by the original terminal observation. -/
noncomputable def canonicalOldLists {C W : ℕ} (lev : Fin C → ℕ) (γ : Fin C → Fin W)
    (B : Fin W → ℝ) (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (N L : ℝ) (i : ℕ) (w : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) : Finset (Fin C) := by
  classical
  exact univ.filter (fun b => lev b = i ∧ γ b = w ∧ o ∈ obs (B w) (δ N L) '' F b)

theorem mem_canonicalOldLists {C W : ℕ} (lev : Fin C → ℕ) (γ : Fin C → Fin W)
    (B : Fin W → ℝ) (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (N L : ℝ) (i : ℕ) (w : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) (b : Fin C) :
    b ∈ canonicalOldLists lev γ B F N L i w o ↔
      lev b = i ∧ γ b = w ∧ o ∈ obs (B w) (δ N L) '' F b := by
  classical
  simp only [canonicalOldLists, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Geometric old lists are measurable even when the original input lists were not
assumed measurable. The frozen polynomial format supplies Borel observation images. -/
theorem measurable_canonicalOldLists {C W D : ℕ} {H : ℝ}
    (lev : Fin C → ℕ) (γ : Fin C → Fin W) (B : Fin W → ℝ)
    (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hfmt : ∀ b q, fmt 7 H D {z : Fin 7 → ℝ | ((q, fun j => z j.castSucc), z 6) ∈ F b})
    (N L : ℝ) (i : ℕ) (w : Fin W) (b : Fin C) :
    MeasurableSet {o | b ∈ canonicalOldLists lev γ B F N L i w o} := by
  have himg : MeasurableSet (obs (B w) (δ N L) '' F b) :=
    Submission.Obl.k4_remainder_pure_profile_normalization.measurableSet_obs_image
      (B w) (δ N L) (hfmt b)
  by_cases hlev : lev b = i
  · by_cases hγ : γ b = w
    · have he : {o | b ∈ canonicalOldLists lev γ B F N L i w o} =
          obs (B w) (δ N L) '' F b := by
        ext o
        simp only [mem_canonicalOldLists, Set.mem_ofPred_eq, hlev, hγ, true_and]
      rw [he]
      exact himg
    · simp only [mem_canonicalOldLists, hγ, and_false, false_and, ofPred_false, MeasurableSet.empty]
  · simp only [mem_canonicalOldLists, hlev, false_and, ofPred_false, MeasurableSet.empty]

/-- The canonical measurable lists inherit the exact original input-list ceiling. -/
theorem card_canonicalOldLists_le {C W : ℕ} (lev : Fin C → ℕ) (γ : Fin C → Fin W)
    (B : Fin W → ℝ) (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (r : ℕ → ℝ)
    (lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C))
    {N L κ : ℝ} (hN : 1 ≤ N)
    (hinput : ∀ b, ∀ p ∈ F b, b ∈ lst (lev b) (γ b) (obs (B (γ b)) (δ N (r (lev b))) p))
    (i : ℕ) (hr : 0 ≤ r i) (hrL : r i ≤ L)
    (hcard : ∀ w o, ((lst i w o).card : ℝ) ≤ κ)
    (w : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
    ((canonicalOldLists lev γ B F N L i w o).card : ℝ) ≤ κ := by
  have hsub : canonicalOldLists lev γ B F N L i w o ⊆
      lst i w (Submission.Lib.K4XInterface.coarsenObs
        (Submission.Lib.K4XInterface.depthIdx N L - Submission.Lib.K4XInterface.depthIdx N (r i)) o) := by
    intro b hb
    obtain ⟨hlev, hγ, p, hp, hpo⟩ := (mem_canonicalOldLists lev γ B F N L i w o b).mp hb
    exact Submission.Lib.K4XInterface.path_charts_met_subset lev γ B F r lst hN hinput
      i hr hrL w o b ⟨hlev, hγ, p, hp, hpo⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcard _ _)

/-- A law supported in an old witness set is supported on the same packet's canonical
list event at the original terminal observation. -/
theorem canonicalOldLists_support {C W : ℕ} (lev : Fin C → ℕ) (γ : Fin C → Fin W)
    (B : Fin W → ℝ) (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (N L : ℝ) (i : ℕ) (b : Fin C) (hlev : lev b = i)
    (μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hsupport : μ (F b)ᶜ = 0) :
    μ {p | b ∉ canonicalOldLists lev γ B F N L i (γ b) (obs (B (γ b)) (δ N L) p)} = 0 := by
  apply measure_mono_null _ hsupport
  intro p hp hF
  exact hp ((mem_canonicalOldLists lev γ B F N L i (γ b) _ b).mpr
    ⟨hlev, rfl, p, hF, rfl⟩)

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
