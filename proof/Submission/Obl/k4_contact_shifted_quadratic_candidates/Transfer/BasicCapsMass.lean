/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/BasicCapsMass.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Mathlib.MeasureTheory.Measure.Real

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set

/-- An original full-label floor also controls the smaller original parent
history reference. Its normalization costs only the inverse floor fraction. -/
theorem original_rho_floor_normalizes {α Ω : Type*}
    [MeasurableSpace α] [MeasurableSpace Ω]
    (ν : Measure α) (ρ : Measure Ω) (A P : Set α) (C : Set Ω)
    {θ q K : ℝ} (hθ : 0 < θ) (hK : θ⁻¹ ≤ K) (hPA : P ⊆ A)
    (hfloor : ENNReal.ofReal (θ * q) * ν A ≤ ρ C) :
    ENNReal.ofReal K⁻¹ * (ENNReal.ofReal q * ν P) ≤ ρ C := by
  have hKi : K⁻¹ ≤ θ := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hθ) hK
  calc
    _ ≤ ENNReal.ofReal θ * (ENNReal.ofReal q * ν P) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hKi) le_rfl
    _ = ENNReal.ofReal (θ * q) * ν P := by rw [ENNReal.ofReal_mul hθ.le, mul_assoc]
    _ ≤ ENNReal.ofReal (θ * q) * ν A := mul_le_mul' le_rfl (measure_mono hPA)
    _ ≤ _ := hfloor

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
