import Mathlib
open scoped ENNReal BigOperators
namespace Submission.Obl.k4_raw_earlier_witness_normalization

theorem card_le_of_mass_packing {ι : Type*} (I : Finset ι) (mass : ι → ENNReal)
    {v K : ℝ} (hv : 0 < v) (hK : 0 ≤ K)
    (hlo : ∀ e ∈ I, ENNReal.ofReal v ≤ mass e)
    (hhi : (∑ e ∈ I, mass e) ≤ ENNReal.ofReal (v * K)) :
    (I.card : ℝ) ≤ K := by
  have hsum : ENNReal.ofReal ((I.card : ℝ) * v) ≤ ENNReal.ofReal (v * K) := by
    calc
      ENNReal.ofReal ((I.card : ℝ) * v) = ∑ _e ∈ I, ENNReal.ofReal v := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        simp [nsmul_eq_mul]
      _ ≤ ∑ e ∈ I, mass e := Finset.sum_le_sum hlo
      _ ≤ _ := hhi
  have hreal := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hv.le hK)).mp hsum
  nlinarith

end Submission.Obl.k4_raw_earlier_witness_normalization
