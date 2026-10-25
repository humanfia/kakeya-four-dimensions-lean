-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/ProjectionMass.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/ProjectionMass.lean (namespace renamed).

import Mathlib

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory Set

/-- A positive mass floor and an original-law density cap force a positive-volume
matched projection. No image of a measurable set is assumed measurable. -/
theorem projection_volume_floor {X : Type*} [MeasurableSpace X]
    (μ ρ : Measure X) (E : Set X) (hE : MeasurableSet E)
    {H m : ℝ} (hH : 0 < H) (hcap : μ ≤ ENNReal.ofReal H • ρ)
    (hsupport : μ Eᶜ = 0) (hmass : ENNReal.ofReal m ≤ μ univ) :
    ENNReal.ofReal (m / H) ≤ ρ E := by
  have hm : ENNReal.ofReal m ≤ ENNReal.ofReal H * ρ E := by
    have htotal : μ univ = μ E := by
      rw [← measure_add_measure_compl hE, hsupport, add_zero]
    rw [htotal] at hmass
    apply hmass.trans
    simpa only [Measure.smul_apply, smul_eq_mul] using (Measure.le_iff'.mp hcap E)
  have hunit : ENNReal.ofReal H⁻¹ * ENNReal.ofReal H = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hH.le), inv_mul_cancel₀ hH.ne']
    norm_num
  calc
    _ = ENNReal.ofReal H⁻¹ * ENNReal.ofReal m := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hH.le)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal H⁻¹ * (ENNReal.ofReal H * ρ E) := by gcongr
    _ = ρ E := by rw [← mul_assoc, hunit, one_mul]

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
