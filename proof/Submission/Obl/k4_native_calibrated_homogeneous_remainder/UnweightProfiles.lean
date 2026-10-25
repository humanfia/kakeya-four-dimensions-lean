import Submission.Obl.k4_native_calibrated_homogeneous_remainder.TypicalOperations

/-! A common world-weight exponent converts a weighted density profile to the
within-world profile needed by the native problem. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Filter
open scoped ENNReal
open Submission.Obl.k4_native_grid_profile_extension.Profiles
open Submission.Obl.k4_scalar_grid_density_extension

theorem typical_unweight {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (μ : (k : ℕ) → Measure (Ω k))
    (ω : (k : ℕ) → Ω k → ℝ) (g : (k : ℕ) → Ω k → ENNReal) (e β : ℝ)
    (ht : HasTypicalDensity N μ (fun k z => ENNReal.ofReal (ω k z) * g k z) e)
    (hω : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ᵐ z ∂μ k,
      N k ^ (-β - ε) ≤ ω k z ∧ ω k z ≤ N k ^ (-β + ε)) :
    HasTypicalDensity N μ g (e - β) := by
  apply typical_of_power_comparison N hN μ _ g e β ht
  intro ε hε
  filter_upwards [hω ε hε] with k hk
  filter_upwards [hk] with z hz
  have hNk : 0 < N k := by linarith [hN k]
  have hlow : ENNReal.ofReal (N k ^ (β - ε)) * ENNReal.ofReal (ω k z) ≤ 1 := by
    calc
      _ ≤ ENNReal.ofReal (N k ^ (β - ε)) * ENNReal.ofReal (N k ^ (-β + ε)) :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hz.2)
      _ = 1 := by
        rw [ofReal_rpow_mul_rpow hNk, show β - ε + (-β + ε) = 0 by ring,
          Real.rpow_zero, ENNReal.ofReal_one]
  have hhigh : (1 : ENNReal) ≤
      ENNReal.ofReal (N k ^ (β + ε)) * ENNReal.ofReal (ω k z) := by
    calc
      _ = ENNReal.ofReal (N k ^ (β + ε)) * ENNReal.ofReal (N k ^ (-β - ε)) := by
        rw [ofReal_rpow_mul_rpow hNk, show β + ε + (-β - ε) = 0 by ring,
          Real.rpow_zero, ENNReal.ofReal_one]
      _ ≤ _ := mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hz.1)
  constructor
  · simpa only [mul_assoc, one_mul] using mul_le_mul' hlow (le_refl (g k z))
  · simpa only [mul_assoc, one_mul] using mul_le_mul' hhigh (le_refl (g k z))

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
