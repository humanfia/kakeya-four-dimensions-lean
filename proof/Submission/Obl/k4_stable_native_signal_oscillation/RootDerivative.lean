import Submission.Obl.k4_stable_native_signal_oscillation.RootCorrection

namespace Submission.Obl.k4_stable_native_signal_oscillation
open MvPolynomial
open Submission.Obl.k4_quadratic_atlas_normalization

lemma rootLift_derivative_bounds (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) {K a : ℝ} (hK : 2 ≤ K) (ha : 0 < a)
    (hc : |curvature P 3| ≤ (K ^ 5 * a)⁻¹)
    (hcglobal : |curvature P 3| ≤ K / a) (p : NativePoint)
    (hr : |value P p| ≤ K * a) (hd : K⁻¹ ≤ |value (pderiv 3 P) p|)
    (hdup : |value (pderiv 3 P) p| ≤ K) (hzero : value P (rootLift P p) = 0) :
    K⁻¹ / 2 ≤ |value (pderiv 3 P) (rootLift P p)| ∧
    |value (pderiv 3 P) (rootLift P p)| ≤ K ^ 2 := by
  have hK0 : 0 < K := by linarith
  have hsame : value (discriminant P 3) (rootLift P p) = value (discriminant P 3) p := by
    exact discriminant_update P hP 3 (fun i => p i)
      (p 3 + rootStep (value P p) (value (pderiv 3 P) p) (curvature P 3))
  have heq := discriminant_eval P 3 (fun i => rootLift P p i)
  change value (discriminant P 3) (rootLift P p) =
    (value (pderiv 3 P) (rootLift P p)) ^ 2 - 2 * curvature P 3 * value P (rootLift P p) at heq
  rw [hzero, mul_zero, sub_zero] at heq
  have hsq : (value (pderiv 3 P) (rootLift P p)) ^ 2 = value (discriminant P 3) p :=
    heq.symm.trans hsame
  have hlo := discriminant_floor P (fun i => p i) 3 hK ha hc hr hd
  have hhi := discriminant_bound P (fun i => p i) 3 hK ha hcglobal hr hdup
  constructor
  · apply (sq_le_sq₀ (by positivity : 0 ≤ K⁻¹ / 2) (abs_nonneg _)).mp
    rw [sq_abs, hsq]
    change (K⁻¹ / 2) ^ 2 ≤ value (discriminant P 3) p
    change (K⁻¹) ^ 2 / 2 ≤ value (discriminant P 3) p at hlo
    nlinarith [sq_nonneg K⁻¹]
  · apply (sq_le_sq₀ (abs_nonneg _) (sq_nonneg K)).mp
    rw [sq_abs, hsq]
    have hupper : value (discriminant P 3) p ≤ K ^ 4 :=
      (le_abs_self _).trans hhi
    nlinarith

end Submission.Obl.k4_stable_native_signal_oscillation
