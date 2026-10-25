/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/FourDirections.lean -/
import Mathlib
import Submission.Obl.k4_matching_endpoint_volume.MatrixEstimates

/-!
# Quantitative scalar cubic tests

The scalar degree-restoration argument in Section 6 of the supplied paper uses
four separated velocity directions. The estimates here recover all four cubic
coefficients with a polynomial loss in the separation and velocity bounds.
-/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

open scoped BigOperators Matrix

/-- Coefficients of a finite polynomial are controlled by a conditioned
Vandermonde matrix and its sampled values. -/
theorem coefficients_le_of_samples {m : ℕ} (v a : Fin m → ℝ)
    {B D E : ℝ} (hB : 1 ≤ B) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hv : ∀ i j : Fin m, |v i ^ (j : ℕ)| ≤ B)
    (hdet : 1 ≤ D * |(Matrix.vandermonde v).det|)
    (ha : ∀ i : Fin m, |∑ j : Fin m, a j * v i ^ (j : ℕ)| ≤ E) :
    ∀ j : Fin m, |a j| ≤ D * ((m : ℝ) * (m.factorial : ℝ) * B ^ m) * E := by
  have hmul := Submission.Obl.k4_matching_endpoint_volume.det_mul_norm_le_mulVec_norm
    (Matrix.vandermonde v) hB (by simpa only [Matrix.vandermonde_apply] using hv) a
  have hvalues : ‖Matrix.vandermonde v *ᵥ a‖ ≤ E := by
    apply (pi_norm_le_iff_of_nonneg hE).mpr
    intro i
    simpa only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply,
      Real.norm_eq_abs, mul_comm] using ha i
  have hcoeff : ‖a‖ ≤ D * ((m : ℝ) * (m.factorial : ℝ) * B ^ m) * E := by
    calc
      ‖a‖ ≤ (D * |(Matrix.vandermonde v).det|) * ‖a‖ := by
        nlinarith [norm_nonneg a]
      _ = D * (|(Matrix.vandermonde v).det| * ‖a‖) := by ring
      _ ≤ D * (((m : ℝ) * (m.factorial : ℝ) * B ^ m) *
          ‖Matrix.vandermonde v *ᵥ a‖) := mul_le_mul_of_nonneg_left hmul hD
      _ ≤ D * (((m : ℝ) * (m.factorial : ℝ) * B ^ m) * E) := by
        gcongr
      _ = _ := by ring
  exact fun j => (norm_le_pi_norm a j).trans hcoeff

/-- The six separation factors in a four-node Vandermonde determinant. -/
theorem cubic_vandermonde_det (v : Fin 4 → ℝ) :
    |(Matrix.vandermonde v).det| =
      |v 1 - v 0| * |v 2 - v 0| * |v 3 - v 0| *
      |v 2 - v 1| * |v 3 - v 1| * |v 3 - v 2| := by
  rw [Matrix.det_vandermonde]
  simp [Fin.prod_univ_succ, Fin.prod_Ioi_succ, mul_assoc]

/-- Four bounded nodes separated by `K⁻¹` have determinant at least `K⁻⁶`. -/
theorem cubic_vandermonde_conditioned (v : Fin 4 → ℝ) {K : ℝ}
    (hK : 0 < K) (hsep : ∀ i j : Fin 4, i ≠ j → K⁻¹ ≤ |v i - v j|) :
    1 ≤ K ^ 6 * |(Matrix.vandermonde v).det| := by
  have hlower : (K⁻¹) ^ 6 ≤ |(Matrix.vandermonde v).det| := by
    rw [cubic_vandermonde_det]
    calc
      (K⁻¹) ^ 6 = K⁻¹ * K⁻¹ * K⁻¹ * K⁻¹ * K⁻¹ * K⁻¹ := by ring
      _ ≤ _ := by
        gcongr
        all_goals exact hsep _ _ (by decide)
  have hm := mul_le_mul_of_nonneg_left hlower (pow_nonneg hK.le 6)
  have heq : K ^ 6 * (K⁻¹) ^ 6 = 1 := by field_simp
  rwa [heq] at hm

/-- Every coefficient of a cubic is bounded by its four velocity tests, with
an explicit polynomial loss. -/
theorem cubic_coefficients_le (v a : Fin 4 → ℝ) {K E : ℝ}
    (hK : 1 ≤ K) (hE : 0 ≤ E) (hv : ∀ i, |v i| ≤ K)
    (hsep : ∀ i j, i ≠ j → K⁻¹ ≤ |v i - v j|)
    (htest : ∀ i, |∑ j : Fin 4, a j * v i ^ (j : ℕ)| ≤ E) :
    ∀ j, |a j| ≤ 96 * K ^ 18 * E := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hbound : ∀ i j : Fin 4, |v i ^ (j : ℕ)| ≤ K ^ 3 := by
    intro i j
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) (hv i) _).trans
      (pow_le_pow_right₀ hK (by omega))
  have h := coefficients_le_of_samples v a (one_le_pow₀ hK)
    (pow_nonneg hK0.le 6) hE hbound (cubic_vandermonde_conditioned v hK0 hsep) htest
  intro j
  calc
    |a j| ≤ K ^ 6 * ((4 : ℝ) * (Nat.factorial 4 : ℝ) * (K ^ 3) ^ 4) * E := h j
    _ = 96 * K ^ 18 * E := by
      have hf : (Nat.factorial 4 : ℝ) = 24 := by norm_num
      rw [hf]
      ring

end Submission.Obl.k4_scalar_grid_parameter_preparation
