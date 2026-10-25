/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file OriginalDensity.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.Model

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open scoped ENNReal

namespace ScalarData

/-- Both density directions for the literal original prepared incidence
law, on every later measurable subset of the prepared event. -/
theorem prepData.original_density_caps {D : ScalarData}
    {H : ℕ → ℝ} {θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine}
    {E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence}
    (hprep : D.prepData H θ E₀) :
    ∀ᶠ k in atTop, ∀ g : Fin (D.W k),
      (D.ρ k g).restrict (E₀ k g) ≤ ENNReal.ofReal (H k) • (θ k g).prod volume ∧
      ∀ E : Set ScalarIncidence, MeasurableSet E → E ⊆ E₀ k g →
        ((θ k g).prod volume) E ≤
          ENNReal.ofReal (H k) * ((D.ρ k g).restrict (E₀ k g)) E := by
  obtain ⟨_, _, hdata⟩ := hprep.2
  filter_upwards [hdata 2 (by norm_num)] with k hk
  intro g
  obtain ⟨_, _, _, _, _, hdenslo, hdensup, _, _⟩ := hk.2 g
  have hH : 0 < H k := lt_of_lt_of_le zero_lt_one (hprep.1.1 k)
  constructor
  · apply Measure.le_iff.mpr
    intro A _
    apply (hdensup A).trans
    rw [Measure.smul_apply, Measure.smul_apply]
    change ENNReal.ofReal (H k) * _ ≤ ENNReal.ofReal (H k) * _
    exact mul_le_mul_right (Measure.restrict_le_self A) _
  · intro E hE hEE
    have hlo := hdenslo E
    rw [Measure.smul_apply, Measure.restrict_apply hE, inter_eq_left.mpr hEE] at hlo
    change ENNReal.ofReal ((H k)⁻¹) * ((θ k g).prod volume) E ≤
      ((D.ρ k g).restrict (E₀ k g)) E at hlo
    have hfactor : ENNReal.ofReal (H k) * ENNReal.ofReal ((H k)⁻¹) = 1 := by
      rw [← ENNReal.ofReal_mul hH.le, mul_inv_cancel₀ hH.ne', ENNReal.ofReal_one]
    calc
      _ = ENNReal.ofReal (H k) *
          (ENNReal.ofReal ((H k)⁻¹) * ((θ k g).prod volume) E) := by
        rw [← mul_assoc, hfactor, one_mul]
      _ ≤ _ := mul_le_mul_right hlo _

end ScalarData

end Submission.Obl.k4_scalar_graph_residual_discovery
