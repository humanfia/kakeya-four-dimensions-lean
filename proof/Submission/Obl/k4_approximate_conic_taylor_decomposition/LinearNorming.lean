/- Adapted from this LOT tree, o144, session x0488, commit 5ed40f2, Submission/Obl/k4_seven_direction_local_degree_restoration/LinearNorming.lean. -/
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Forms

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition

open MvPolynomial

/-- The continuous linear form with the given three coordinate coefficients. -/
noncomputable def linearForm (a : Fin 3 → ℝ) : E3 →L[ℝ] ℝ :=
  ∑ i : Fin 3, a i • (EuclideanSpace.proj i : E3 →L[ℝ] ℝ)

lemma linearForm_apply (a : Fin 3 → ℝ) (u : E3) :
    linearForm a u = ∑ i : Fin 3, a i * u i := by
  simp [linearForm]

lemma linearForm_norm_le {a : Fin 3 → ℝ} {B : ℝ} (hB : 0 ≤ B) (ha : ∀ i, |a i| ≤ B) :
    ‖linearForm a‖ ≤ 3 * B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [linearForm_apply, Real.norm_eq_abs]
  calc
    |∑ i : Fin 3, a i * u i| ≤ ∑ i : Fin 3, |a i * u i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin 3, B * ‖u‖ := by
      refine Finset.sum_le_sum fun i hi => ?_
      rw [abs_mul]
      exact mul_le_mul (ha i) (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i)
        (abs_nonneg _) hB
    _ = (3 * B) * ‖u‖ := by simp; ring

lemma norm_linearForm_of_coefficients (P : MvPolynomial (Fin 3) ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hcoeff : ∀ i : Fin 3, |P.coeff (Finsupp.single i 1)| ≤ B) :
    ‖linearForm (fun i => P.coeff (Finsupp.single i 1))‖ ≤ 3 * B :=
  linearForm_norm_le hB hcoeff

end Submission.Obl.k4_approximate_conic_taylor_decomposition
