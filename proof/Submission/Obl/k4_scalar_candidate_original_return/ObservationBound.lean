import Submission.Obl.k4_scalar_candidate_original_return.ObservationCoordinates

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

/-- Bounded original coefficients and unit time give bounded full observation
coordinates, including the quadratic hidden position. -/
lemma observationShear_bound {R : ℝ} (hR : 1 ≤ R) (a : Fin 5 → ℝ)
    (ha : ∀ i, |a i| ≤ R) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ i, |observationShear (a, t) i| ≤ 3 * R := by
  have hR0 : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 1).trans hR
  have hta : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have ht2 : |t ^ 2| ≤ 1 := by
    rw [abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg t) hta 2
  have hprod (i : Fin 5) : |t * a i| ≤ R := by
    rw [abs_mul]
    calc
      _ ≤ 1 * R := mul_le_mul hta (ha i) (abs_nonneg _) (by norm_num)
      _ = R := one_mul _
  have hprod2 (i : Fin 5) : |t ^ 2 * a i| ≤ R := by
    rw [abs_mul]
    calc
      _ ≤ 1 * R := mul_le_mul ht2 (ha i) (abs_nonneg _) (by norm_num)
      _ = R := one_mul _
  rw [observationShear_apply]
  intro i
  fin_cases i
  · exact hta.trans (by linarith)
  · exact (abs_add_le _ _).trans (by linarith [ha 0, hprod 1])
  · exact (ha 1).trans (by linarith)
  · exact (abs_add_le _ _).trans
      (by linarith [abs_add_le (a 2) (t * a 3), ha 2, hprod 3, hprod2 4])
  · exact (ha 3).trans (by linarith)
  · exact (ha 4).trans (by linarith)

end Submission.Obl.k4_scalar_candidate_original_return
