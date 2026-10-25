/- Adapted from this LOT tree, o151, session x0508, commit 274d45f,
   Submission/Obl/k4_known_atlas_normalization_composition/MassCalibration.lean. Earlier provenance comments are retained. -/
import Mathlib

namespace Submission.Obl.k4_native_finite_terminal_atlas_lift

/-- The within-world terminal calibration turns a child floor into the original
floor after multiplying by time length and FULL prior assignment mass. -/
theorem floor_calibration_real {n n' J J' m a b κ κ' : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hκ : 0 < κ) (hκ' : 0 < κ')
    (hJ' : 0 ≤ J') (hcal : n * J ≤ κ * m * n') :
    n * (J * J') / (a * b * (κ * κ')) ≤
      (m / a) * (n' * J' / (b * κ')) := by
  calc
    _ = (n * J) * J' / (a * b * (κ * κ')) := by ring
    _ ≤ (κ * m * n') * J' / (a * b * (κ * κ')) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcal hJ') (by positivity)
    _ = _ := by field_simp <;> ring

theorem floor_calibration {n n' J J' m a b κ κ' : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hκ : 0 < κ) (hκ' : 0 < κ')
    (hm : 0 ≤ m) (hJ' : 0 ≤ J') (hcal : n * J ≤ κ * m * n')
    {mass : ENNReal} (hfloor : ENNReal.ofReal (n' * J' / (b * κ')) ≤ mass) :
    ENNReal.ofReal (n * (J * J') / (a * b * (κ * κ'))) ≤
      ENNReal.ofReal (m / a) * mass := by
  calc
    _ ≤ ENNReal.ofReal ((m / a) * (n' * J' / (b * κ'))) :=
      ENNReal.ofReal_le_ofReal (floor_calibration_real ha hb hκ hκ' hJ' hcal)
    _ = ENNReal.ofReal (m / a) * ENNReal.ofReal (n' * J' / (b * κ')) :=
      ENNReal.ofReal_mul (div_nonneg hm ha.le)
    _ ≤ _ := mul_le_mul' le_rfl hfloor

/-- The mixture normalizer belongs in the world weights. It cancels from the
within-world conversion only after those original weights are restored. -/
theorem weighted_conditional_mass {ω ω' q m Z : ℝ} (hω : 0 ≤ ω) (hZ : 0 < Z)
    (hweights : ω' = ω * q * m / Z) (mass : ENNReal) :
    ENNReal.ofReal ω * (ENNReal.ofReal (q * m) * mass) =
      ENNReal.ofReal Z * (ENNReal.ofReal ω' * mass) := by
  have hreal : ω * (q * m) = Z * ω' := by
    rw [hweights]
    field_simp <;> ring
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hω,
    ← ENNReal.ofReal_mul hZ.le, hreal]

/-- Inverse-subpower retained mass is preserved by the original world mixture. -/
theorem retained_mass_lift {κ κ' Z : ℝ} (hκ : 0 < κ) (hκ' : 0 < κ')
    (hZ : κ⁻¹ ≤ Z) {mass : ENNReal} (hfloor : ENNReal.ofReal κ'⁻¹ ≤ mass) :
    ENNReal.ofReal (κ * κ')⁻¹ ≤ ENNReal.ofReal Z * mass := by
  calc
    _ = ENNReal.ofReal κ⁻¹ * ENNReal.ofReal κ'⁻¹ := by
      rw [mul_inv, ENNReal.ofReal_mul (inv_nonneg.mpr hκ.le)]
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hZ) hfloor

end Submission.Obl.k4_native_finite_terminal_atlas_lift
