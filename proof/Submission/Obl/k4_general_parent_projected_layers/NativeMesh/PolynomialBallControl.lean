/- Adapted from this LOT tree o222, session x0774, commit 109e510d,
   Submission/Obl/k4_projected_parent_contact_reduction/PolynomialBallControl.lean.
   Existing source attributions are retained below. Accepted mesh-saturation
   results are imported from Submission.Lib.K4AffineMeshCaps.Saturation. -/
import Submission.Lib.K4PolynomialRemezThree.PolynomialNorm
import Submission.Obl.k4_stable_native_signal_oscillation.PolynomialBounds
import Submission.Obl.k4_stable_native_signal_oscillation.Dilation
import Submission.Obl.k4_stable_native_signal_oscillation.PowerBounds
import Submission.Obl.k4_stable_quadratic_hidden_sheets.Sheet

/-! Polynomial value and Lipschitz control from a fixed-power coefficient bound. -/

namespace Submission.Obl.k4_general_parent_projected_layers.NativeMesh


open MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_stable_quadratic_hidden_sheets (eval₂_ofReal coord_le_of_norm_le)

noncomputable section

theorem coefficient_power_ball_control (D n : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ K E : ℝ, 2 ≤ K → 0 ≤ E →
      ∀ P : MvPolynomial (Fin 3) ℝ, P.totalDegree ≤ D →
        (∀ e, |P.coeff e| ≤ K ^ n * E) →
        (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 3 * K →
          |eval (fun i => x i) P| ≤ K ^ N * E) ∧
        ∀ x y : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 3 * K → ‖y‖ ≤ 3 * K →
          |eval (fun i => x i) P - eval (fun i => y i) P| ≤ K ^ N * E * ‖x - y‖ := by
  obtain ⟨L₀, hL₀, hlip⟩ := exists_polynomial_lipschitz_of_ball_bound D
  let C : ℝ := (((D + 1 : ℕ) : ℝ) ^ 3) * (3 : ℝ) ^ D
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨N, hN, hpower⟩ := exists_nat_power_bound ((L₀ + 1) * C) (D + n)
  refine ⟨N, hN, ?_⟩
  intro K E hK hE P hP hcoeff
  have hK0 : 0 < K := by linarith
  have h3K : 0 < 3 * K := by positivity
  have h3K1 : 1 ≤ 3 * K := by linarith
  have hpower' := hpower K hK
  rw [← Nat.cast_add, Real.rpow_natCast] at hpower'
  have hB : 0 ≤ C * K ^ (D + n) := by positivity
  have hvalue : C * K ^ (D + n) ≤ K ^ N := by
    apply le_trans _ hpower'
    nlinarith [mul_nonneg hL₀.le hB]
  have hloss : L₀ * (C * K ^ (D + n)) ≤ K ^ N := by
    apply le_trans _ hpower'
    nlinarith
  have hgrowth (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ ≤ 3 * K) :
      |eval (fun i => x i) P| ≤ C * K ^ (D + n) * E := by
    have h := Submission.Lib.K4PolynomialRemezThree.norm_complex_eval_le_of_coeff_bound
      3 D P hP (by positivity : 0 ≤ K ^ n * E) h3K1 hcoeff
      (fun i => (x i : ℂ)) (coord_le_of_norm_le x (3 * K) hx)
    have hreal : ‖eval₂ (algebraMap ℝ ℂ) (fun i => (x i : ℂ)) P‖ =
        |eval (fun i => x i) P| := by
      rw [eval₂_ofReal, Complex.norm_real, Real.norm_eq_abs]
    rw [hreal] at h
    apply h.trans_eq
    dsimp [C]
    rw [mul_pow, pow_add]
    ring
  constructor
  · intro x hx
    exact (hgrowth x hx).trans (mul_le_mul_of_nonneg_right hvalue hE)
  · intro x y hx hy
    let Q := dilatePolynomial (3 * K) P
    let V : ℝ := C * K ^ (D + n) * E
    have hQ : Q.totalDegree ≤ D := (dilatePolynomial_degree _ _).trans hP
    have hQbound (u : EuclideanSpace ℝ (Fin 3)) (hu : ‖u‖ ≤ 1 / 8) :
        |eval (fun i => u i) Q| ≤ V := by
      have hnu : ‖(3 * K) • u‖ ≤ 3 * K := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos h3K]
        nlinarith
      simpa only [Q, eval_dilatePolynomial, PiLp.smul_apply, smul_eq_mul] using
        hgrowth ((3 * K) • u) hnu
    have hnorm (z : EuclideanSpace ℝ (Fin 3)) (hz : ‖z‖ ≤ 3 * K) :
        ‖(3 * K)⁻¹ • z‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h3K)]
      calc
        _ ≤ (3 * K)⁻¹ * (3 * K) := mul_le_mul_of_nonneg_left hz (by positivity)
        _ = 1 := inv_mul_cancel₀ h3K.ne'
    have h := hlip Q hQ V (by dsimp [V]; positivity) hQbound
      ((3 * K)⁻¹ • x) ((3 * K)⁻¹ • y) (hnorm x hx) (hnorm y hy)
    dsimp only [Q] at h
    rw [eval_dilatePolynomial_inv _ h3K.ne', eval_dilatePolynomial_inv _ h3K.ne'] at h
    have hdist : ‖(3 * K)⁻¹ • x - (3 * K)⁻¹ • y‖ ≤ ‖x - y‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h3K)]
      exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ h3K1)
    calc
      _ ≤ L₀ * V * ‖(3 * K)⁻¹ • x - (3 * K)⁻¹ • y‖ := h
      _ ≤ L₀ * V * ‖x - y‖ := mul_le_mul_of_nonneg_left hdist (by dsimp [V]; positivity)
      _ = (L₀ * (C * K ^ (D + n))) * E * ‖x - y‖ := by dsimp [V]; ring
      _ ≤ K ^ N * E * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hloss hE) (norm_nonneg _)

end

end Submission.Obl.k4_general_parent_projected_layers.NativeMesh
