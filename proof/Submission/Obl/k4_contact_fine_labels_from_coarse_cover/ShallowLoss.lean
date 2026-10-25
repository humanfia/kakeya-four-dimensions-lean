-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/ShallowLoss.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.CalibrationLoss
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelScales

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model

open Filter

variable {α : Type*} [MeasurableSpace α] (p : Model α)

/-- A shallow ORIGINAL mass floor costs a fixed power of that shallow depth.
The universal real calibration exponent falls on the subpower budget only. -/
theorem eventually_shallow_calibration_loss (hp : p.Valid) {C s : ℝ}
    (hC : 1 ≤ C) (hs : 0 < s) :
    ∀ᶠ k in atTop, C * (1 + 2 * p.K k) ^ C *
      (1 + ((2 * p.K k + 5) * p.K k) / p.N k ^ (-6 * s)) ^ (6 : ℕ) ≤
        p.N k ^ (37 * s) := by
  filter_upwards [eventually_calibration_loss_le p hp hC hs] with k hk
  have hN := Valid.N_pos p hp k
  have hK := Valid.K_pos p hp k
  let β := (2 * p.K k + 5) * p.K k
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hpow : 1 ≤ p.N k ^ (6 * s) :=
    Real.one_le_rpow (by linarith [hp.N_ge k]) (by linarith)
  have hinv : (p.N k ^ (-6 * s))⁻¹ = p.N k ^ (6 * s) := by
    rw [show -6 * s = -(6 * s) by ring, Real.rpow_neg hN.le, inv_inv]
  have hβK : β ≤ β / (p.K k)⁻¹ := by
    simpa only [div_inv_eq_mul, mul_one] using
      mul_le_mul_of_nonneg_left (hp.K_ge k) hβ
  have hfactor : 1 + β / p.N k ^ (-6 * s) ≤
      (1 + β / (p.K k)⁻¹) * p.N k ^ (6 * s) := by
    rw [div_eq_mul_inv, hinv]
    calc
      _ ≤ p.N k ^ (6 * s) + (β / (p.K k)⁻¹) * p.N k ^ (6 * s) :=
        add_le_add hpow (mul_le_mul_of_nonneg_right hβK (Real.rpow_nonneg hN.le _))
      _ = _ := by ring
  have hpow6 : (p.N k ^ (6 * s)) ^ (6 : ℕ) = p.N k ^ (36 * s) := by
    rw [← Real.rpow_mul_natCast hN.le]
    congr 1
    ring
  calc
    _ ≤ C * (1 + 2 * p.K k) ^ C *
        ((1 + β / (p.K k)⁻¹) * p.N k ^ (6 * s)) ^ (6 : ℕ) := by
      apply mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hfactor 6)
      positivity
    _ = (C * (1 + 2 * p.K k) ^ C * (1 + β / (p.K k)⁻¹) ^ (6 : ℕ)) *
        p.N k ^ (36 * s) := by rw [mul_pow, hpow6]; ring
    _ ≤ p.N k ^ s * p.N k ^ (36 * s) :=
      mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hN.le _)
    _ = _ := by rw [← Real.rpow_add hN]; congr 1; ring

theorem eventually_shallow_calibration_mesh (hp : p.Valid) {C s : ℝ}
    (hC : 1 ≤ C) (hs : 0 < s) :
    ∀ᶠ k in atTop, C * (1 + 2 * p.K k) ^ C *
      (1 + ((2 * p.K k + 5) * p.K k) / p.N k ^ (-6 * s)) ^ (6 : ℕ) *
        p.N k ^ (-100 * s) ≤ (1 : ℝ) / 2 := by
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hp.N_lim (show -63 * s < 0 by linarith) (2 : ℝ)
  filter_upwards [eventually_shallow_calibration_loss p hp hC hs, hsmall] with k hk hsmall
  simp only [Real.rpow_zero] at hsmall
  have hN := Valid.N_pos p hp k
  calc
    _ ≤ p.N k ^ (37 * s) * p.N k ^ (-100 * s) :=
      mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hN.le _)
    _ = p.N k ^ (-63 * s) := by rw [← Real.rpow_add hN]; congr 1; ring
    _ ≤ 1 / 2 := by linarith

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover.Model
