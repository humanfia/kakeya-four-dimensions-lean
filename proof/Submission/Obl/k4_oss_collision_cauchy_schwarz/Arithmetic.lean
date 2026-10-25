import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace Submission.Obl.k4_oss_collision_cauchy_schwarz

/-- The elementary square inequality, including infinite nonnegative values. -/
theorem two_mul_mul_le_add_mul_self (a b : ℝ≥0∞) :
    2 * (a * b) ≤ a * a + b * b := by
  by_cases ha : a = ⊤
  · simp [ha]
  by_cases hb : b = ⊤
  · simp [hb]
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  norm_cast
  exact_mod_cast (by nlinarith [sq_nonneg ((a : ℝ) - (b : ℝ))] :
    2 * ((a : ℝ) * (b : ℝ)) ≤ (a : ℝ) * a + (b : ℝ) * b)

/-- An integer shift cannot increase the square correlation sum. -/
theorem tsum_mul_shift_le (a : ℤ → ℝ≥0∞) (j : ℤ) :
    (∑' k, a k * a (k + j)) ≤ ∑' k, a k * a k := by
  have h : 2 * (∑' k, a k * a (k + j)) ≤ 2 * (∑' k, a k * a k) := calc
    _ = ∑' k, 2 * (a k * a (k + j)) := ENNReal.tsum_mul_left.symm
    _ ≤ ∑' k, (a k * a k + a (k + j) * a (k + j)) :=
      ENNReal.tsum_le_tsum fun k => two_mul_mul_le_add_mul_self _ _
    _ = (∑' k, a k * a k) + ∑' k, a (k + j) * a (k + j) := ENNReal.tsum_add
    _ = (∑' k, a k * a k) + ∑' k, a k * a k := by
      congr 1
      simpa using (Equiv.addRight j).tsum_eq (fun k => a k * a k)
    _ = 2 * (∑' k, a k * a k) := (two_mul _).symm
  exact (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp h

/-- Jensen's square inequality for a probability measure, in nonnegative integrals. -/
theorem lintegral_mul_self_le {P : Type*} [MeasurableSpace P]
    (π : Measure P) [IsProbabilityMeasure π] {f : P → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂π) * (∫⁻ p, f p ∂π) ≤ ∫⁻ p, f p * f p ∂π := by
  have h :
      (∫⁻ p, ∫⁻ q, 2 * (f p * f q) ∂π ∂π) ≤
      ∫⁻ p, ∫⁻ q, (f p * f p + f q * f q) ∂π ∂π :=
    lintegral_mono fun p => lintegral_mono fun q =>
      two_mul_mul_le_add_mul_self _ _
  have hleft : (∫⁻ p, ∫⁻ q, 2 * (f p * f q) ∂π ∂π) =
      2 * ((∫⁻ p, f p ∂π) * ∫⁻ p, f p ∂π) := by
    simp_rw [lintegral_const_mul _ (hf.const_mul _)]
    rw [lintegral_const_mul _ (by fun_prop)]
    rw [lintegral_lintegral_mul hf.aemeasurable hf.aemeasurable]
  have hright : (∫⁻ p, ∫⁻ q, (f p * f p + f q * f q) ∂π ∂π) =
      2 * (∫⁻ p, f p * f p ∂π) := by
    simp_rw [lintegral_add_left measurable_const _, lintegral_const,
      measure_univ, mul_one]
    rw [lintegral_add_left (show Measurable (fun p => f p * f p) from hf.mul hf) _]
    simp [two_mul]
  rw [hleft, hright] at h
  exact (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp h

end Submission.Obl.k4_oss_collision_cauchy_schwarz
