/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file OriginalWorldChoice.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open scoped ENNReal

/-- A dense original weighted mixture contains a full-prior component of
comparable relative density. Neither the weights nor the priors are replaced. -/
theorem exists_original_weighted_dense_component {ι : Type*}
    (weight prior mass : ι → ℝ≥0∞) {δ : ℝ} (hδ : 0 < δ)
    (hprior : (∑' i, weight i * prior i) ≤ 1)
    (hmass : ENNReal.ofReal δ ≤ ∑' i, weight i * mass i)
    (hzero : ∀ i, prior i = 0 → mass i = 0) :
    ∃ i, weight i ≠ 0 ∧ prior i ≠ 0 ∧ ENNReal.ofReal (δ / 2) * prior i ≤ mass i := by
  classical
  by_contra h
  have hpoint (i : ι) : weight i * mass i ≤ ENNReal.ofReal (δ / 2) * (weight i * prior i) := by
    by_cases hw : weight i = 0
    · simp only [hw, zero_mul, mul_zero, le_refl]
    by_cases hp : prior i = 0
    · simp only [hp, hzero i hp, mul_zero, le_refl]
    have hi : mass i ≤ ENNReal.ofReal (δ / 2) * prior i :=
      (lt_of_not_ge (fun hi => h ⟨i, hw, hp, hi⟩)).le
    calc
      _ ≤ weight i * (ENNReal.ofReal (δ / 2) * prior i) :=
        mul_le_mul_of_nonneg_left hi zero_le
      _ = _ := by ring
  have hbound : (∑' i, weight i * mass i) ≤ ENNReal.ofReal (δ / 2) := by
    calc
      _ ≤ ∑' i, ENNReal.ofReal (δ / 2) * (weight i * prior i) := ENNReal.tsum_le_tsum hpoint
      _ = ENNReal.ofReal (δ / 2) * ∑' i, weight i * prior i := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (δ / 2) * 1 := mul_le_mul_of_nonneg_left hprior zero_le
      _ = _ := mul_one _
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmass.trans hbound)
  rw [ENNReal.toReal_ofReal hδ.le, ENNReal.toReal_ofReal (by positivity : 0 ≤ δ / 2)] at hreal
  linarith

end Submission.Obl.k4_scalar_graph_residual_discovery
