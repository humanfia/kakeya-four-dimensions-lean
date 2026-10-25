import Submission.Obl.k4_quadratic_mesh_coefficient_calibration.OccupiedGridCalibration
import Submission.Lib.K4ChartLifting.Normalize

/-! Calibration in original base coordinates. The artificial cube coordinates
have a coefficient-contractive inverse when the original base bound is at
least one. No bound on the coefficients to be calibrated is assumed.

Adapted from: here:o200 (session x0829, commit 546fbde3; as at commit 6f32949a),
file `Submission/Obl/k4_finite_projected_horizontal_candidates/RawGridCalibration.lean`,
moved into this obligation's namespace. -/

namespace Submission.Obl.k4_quadratic_mesh_coefficient_calibration

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ChartLifting
open Submission.Lib.K4CommonLocalChoice (cell)

noncomputable section

def calibrationForward (H : ℝ) (i : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  C (8 * H)⁻¹ * X i + C (1 / 4)

def calibrationBackward (H : ℝ) (i : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  C (8 * H) * X i - C (2 * H)

def calibrationPolynomial (H : ℝ) (P : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ := bind₁ (calibrationBackward H) P

theorem calibrationPolynomial_degree (H : ℝ) (P : MvPolynomial (Fin 3) ℝ) :
    (calibrationPolynomial H P).totalDegree ≤ P.totalDegree := by
  apply totalDegree_bind₁_le_of_le_one
  intro i
  exact deg1_sub (deg1_C_mul _ (deg1_X i)) (deg1_C _)

theorem eval_calibrationPolynomial {H : ℝ} (hH : 0 < H)
    (P : MvPolynomial (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    eval (calibrationBase H x) (calibrationPolynomial H P) = eval x P := by
  rw [calibrationPolynomial, eval_bind₁']
  apply congrArg (fun y => eval y P)
  funext i
  simp only [calibrationBackward, eval_sub, eval_mul, eval_C, eval_X, calibrationBase]
  field_simp
  ring

theorem calibrationPolynomial_return {H : ℝ} (hH : 0 < H)
    (P : MvPolynomial (Fin 3) ℝ) :
    bind₁ (calibrationForward H) (calibrationPolynomial H P) = P := by
  rw [calibrationPolynomial, bind₁_bind₁]
  have hi : (fun i => bind₁ (calibrationForward H) (calibrationBackward H i)) = X := by
    funext i
    unfold calibrationBackward
    rw [map_sub, map_mul, bind₁_C_right, bind₁_X_right, bind₁_C_right]
    unfold calibrationForward
    calc
      C (8 * H) * (C (8 * H)⁻¹ * X i + C (1 / 4)) - C (2 * H) =
          C ((8 * H) * (8 * H)⁻¹) * X i + C ((8 * H) * (1 / 4)) - C (2 * H) := by
            simp only [map_mul]; ring
      _ = X i := by
        rw [mul_inv_cancel₀ (by positivity : (8 : ℝ) * H ≠ 0),
          show (8 * H) * (1 / 4 : ℝ) = 2 * H by ring]
        simp
  rw [hi, bind₁_X_left]
  rfl

theorem coeffL1_calibrationForward {H : ℝ} (hH : 1 ≤ H) (i : Fin 3) :
    coeffL1 (calibrationForward H i) ≤ 1 := by
  have hp : 0 < 8 * H := by linarith
  have hb : (8 * H)⁻¹ ≤ 1 / 8 := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 8) (by linarith : (8 : ℝ) ≤ 8 * H)
  calc
    _ ≤ coeffL1 (C (8 * H)⁻¹ * X i) + coeffL1 (C (1 / 4)) := coeffL1_add_le _ _
    _ ≤ |(8 * H)⁻¹| * coeffL1 (X i) + |(1 / 4 : ℝ)| := by
      rw [coeffL1_C]
      exact add_le_add (coeffL1_C_mul_le _ _) le_rfl
    _ ≤ 1 := by
      rw [coeffL1_X, mul_one, abs_of_pos (inv_pos.mpr hp),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      linarith

/-- Returning to original coordinates costs no coefficient norm: the
normalizing map has coefficients of total absolute value at most one. -/
theorem coeffL1_le_calibrationPolynomial {H : ℝ} (hH : 1 ≤ H)
    (P : MvPolynomial (Fin 3) ℝ) :
    coeffL1 P ≤ coeffL1 (calibrationPolynomial H P) := by
  have hh := coeffL1_bind₁_le (calibrationForward H) 1 le_rfl
    (coeffL1_calibrationForward hH) (calibrationPolynomial H P)
  rw [calibrationPolynomial_return (zero_lt_one.trans_le hH) P] at hh
  simpa only [one_pow, mul_one] using hh

/-- Coefficients in the ORIGINAL coordinates, derived from ORIGINAL grid
caps and a.e. actual polynomial values. -/
theorem exists_raw_coefficient_bound_from_original_grid (D : ℕ) :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ)
        (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
      ∀ H h m beta E : ℝ, 1 ≤ H → 0 < h → h ≤ H →
        0 < m → 0 < beta → m ≤ beta * (8 * H) ^ 3 → 0 ≤ E →
        ENNReal.ofReal m ≤ μ univ →
        (∀ q : Fin 3 → ℤ,
          μ {p | cell h (Z p) = q} ≤ ENNReal.ofReal (beta * h ^ 3)) →
        (∀ᵐ p ∂μ, (∀ j, |Z p j| ≤ H) ∧ |eval (Z p) P| ≤ E) →
        2 * L * ((D + 1) ^ 3 : ℕ) * C *
          (32 * ((D : ℝ) + 1) / (m / (beta * (8 * H) ^ 3))) ^ (3 * D) *
            (h / (8 * H)) ≤ 1 / 2 →
        ∀ e, |P.coeff e| ≤ ((D + 1) ^ 3 : ℕ) *
          (2 * ((D + 1) ^ 3 : ℕ) * C *
            (32 * ((D : ℝ) + 1) / (m / (beta * (8 * H) ^ 3))) ^ (3 * D) * E) := by
  obtain ⟨C, L, hC, hL, hcal⟩ := exists_coefficient_bound_from_original_grid D
  refine ⟨C, L, hC, hL, ?_⟩
  intro Ω _ μ Z P hP H h m beta E hH hh hhH hm hbeta hmb hE hmass hcap hgood hsmall e
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hdeg : (calibrationPolynomial H P).totalDegree ≤ D :=
    (calibrationPolynomial_degree H P).trans hP
  have hgood' : ∀ᵐ p ∂μ, (∀ j, |Z p j| ≤ H) ∧
      |eval (calibrationBase H (Z p)) (calibrationPolynomial H P)| ≤ E := by
    simpa only [eval_calibrationPolynomial hHp] using hgood
  have hc := hcal Ω μ Z (calibrationPolynomial H P) hdeg H h m beta E hHp hh hhH hm
    hbeta hmb hE hmass hcap hgood' hsmall
  exact (abs_coeff_le_coeffL1 P e).trans ((coeffL1_le_calibrationPolynomial hH P).trans
    (coeffL1_le_of_coeff_le (calibrationPolynomial H P) hdeg _ hc))

end
end Submission.Obl.k4_quadratic_mesh_coefficient_calibration
