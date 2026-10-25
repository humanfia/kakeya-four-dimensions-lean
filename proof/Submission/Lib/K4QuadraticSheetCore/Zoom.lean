import Mathlib
import Submission.Lib.K4ContactNormalization

/-! Adapted from: here:o223 (session x0777, branch x0777). -/

/-!
# Heisenberg zoom of a true block

The time interval `[t₀, t₀ + q]` of a true block is rescaled to `[0, 1]`. The horizontal
coordinate `Z` is translated by `Z₀` and divided by `q`; the transverse coordinate `Y` is
moved by the Heisenberg translation `Y ↦ Y - Y₀ + Z₀ t - t₀ Z` and divided by `q ^ 2`.
The hidden coordinate is unchanged here; the residual normalization of
`Submission.Lib.K4ContactNormalization` acts on it separately.

Lines go to lines, the velocity `b 3` is unchanged (so velocity bins and the palette are
unchanged), the contact error `b 4 + b 0` is divided by `q`, and a velocity strip
transports to a velocity strip with the same width times `q`.
-/

namespace Submission.Lib.K4QuadraticSheetCore

open MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4ChartLifting

noncomputable section

/-- New line coefficients after the Heisenberg zoom of the block with left time `t₀`,
length `q`, horizontal centre `Z₀` and transverse centre `Y₀`. -/
def zoomCoeff (t₀ q Z₀ Y₀ : ℝ) (b : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![(b 0 + t₀ * b 3 - Z₀) / q,
    (b 1 - Y₀ - t₀ * b 0 + t₀ * b 4 + t₀ * Z₀ - t₀ ^ 2 * b 3) / q ^ 2,
    b 2 + t₀ * b 5,
    b 3,
    (b 4 + Z₀ - t₀ * b 3) / q,
    q * b 5]

/-- The new coordinates as polynomials in the old ones. -/
def zoomSubst (t₀ q Z₀ Y₀ : ℝ) : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![C q⁻¹ * (X 0 - C t₀),
    C q⁻¹ * (X 1 - C Z₀),
    C (q ^ 2)⁻¹ * (X 2 - C Y₀ + C Z₀ * X 0 - C t₀ * X 1),
    X 3]

/-- The new time of an old time. -/
def zoomTime (t₀ q t : ℝ) : ℝ := (t - t₀) / q

theorem eval_zoomSubst (t₀ q Z₀ Y₀ : ℝ) (hq : q ≠ 0) (b : Fin 6 → ℝ) (t : ℝ) :
    (fun i => eval (point b t) (zoomSubst t₀ q Z₀ Y₀ i)) =
      point (zoomCoeff t₀ q Z₀ Y₀ b) (zoomTime t₀ q t) := by
  funext i
  fin_cases i <;> simp [zoomSubst, point, zoomCoeff, zoomTime] <;> field_simp <;> ring

/-- The zoom keeps the velocity coordinate. -/
theorem zoomCoeff_three (t₀ q Z₀ Y₀ : ℝ) (b : Fin 6 → ℝ) :
    zoomCoeff t₀ q Z₀ Y₀ b 3 = b 3 := rfl

/-- The contact error is divided by the block length. -/
theorem zoomCoeff_contact (t₀ q Z₀ Y₀ : ℝ) (hq : q ≠ 0) (b : Fin 6 → ℝ) :
    zoomCoeff t₀ q Z₀ Y₀ b 4 + zoomCoeff t₀ q Z₀ Y₀ b 0 = (b 4 + b 0) / q := by
  simp only [zoomCoeff, Matrix.cons_val]
  field_simp
  ring

/-- A velocity strip in the new chart is a velocity strip in the old chart. -/
theorem zoomCoeff_strip (t₀ q Z₀ Y₀ : ℝ) (hq : 0 < q) (b : Fin 6 → ℝ) (z : Fin 2 → ℝ) :
    |zoomCoeff t₀ q Z₀ Y₀ b 4 - z 0 - z 1 * zoomCoeff t₀ q Z₀ Y₀ b 3| =
      |b 4 - (q * z 0 - Z₀) - (q * z 1 + t₀) * b 3| / q := by
  simp only [zoomCoeff, Matrix.cons_val]
  rw [← abs_of_pos hq, ← abs_div, abs_of_pos hq]
  congr 1
  field_simp
  ring

/-- The polynomial in old coordinates of a test in new coordinates. -/
def zoomLift (t₀ q Z₀ Y₀ : ℝ) (Q : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  bind₁ (zoomSubst t₀ q Z₀ Y₀) Q

theorem zoomSubst_degree (t₀ q Z₀ Y₀ : ℝ) (i : Fin 4) :
    (zoomSubst t₀ q Z₀ Y₀ i).totalDegree ≤ 1 := by
  fin_cases i
  · exact deg1_C_mul _ (deg1_sub (deg1_X _) (deg1_C _))
  · exact deg1_C_mul _ (deg1_sub (deg1_X _) (deg1_C _))
  · exact deg1_C_mul _ (deg1_sub (deg1_add (deg1_sub (deg1_X _) (deg1_C _))
      (deg1_C_mul _ (deg1_X _))) (deg1_C_mul _ (deg1_X _)))
  · exact deg1_X _

theorem zoomLift_degree (t₀ q Z₀ Y₀ : ℝ) (Q : MvPolynomial (Fin 4) ℝ) :
    (zoomLift t₀ q Z₀ Y₀ Q).totalDegree ≤ Q.totalDegree :=
  totalDegree_bind₁_le_of_le_one _ (zoomSubst_degree t₀ q Z₀ Y₀) Q

theorem eval_zoomLift (t₀ q Z₀ Y₀ : ℝ) (hq : q ≠ 0) (Q : MvPolynomial (Fin 4) ℝ)
    (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point b t) (zoomLift t₀ q Z₀ Y₀ Q) =
      eval (point (zoomCoeff t₀ q Z₀ Y₀ b) (zoomTime t₀ q t)) Q := by
  rw [zoomLift, eval_bind₁', eval_zoomSubst t₀ q Z₀ Y₀ hq]

/-- Only the hidden coordinate of the zoom depends on the hidden variable. -/
theorem pderiv_zoomSubst (t₀ q Z₀ Y₀ : ℝ) (i : Fin 4) :
    pderiv (3 : Fin 4) (zoomSubst t₀ q Z₀ Y₀ i) = if i = 3 then 1 else 0 := by
  fin_cases i <;> simp [zoomSubst, pderiv_X]

theorem pderiv_zoomLift (t₀ q Z₀ Y₀ : ℝ) (Q : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (zoomLift t₀ q Z₀ Y₀ Q) =
      zoomLift t₀ q Z₀ Y₀ (pderiv 3 Q) := by
  rw [zoomLift, zoomLift, pderiv_bind₁, Finset.sum_eq_single (3 : Fin 4)]
  · rw [pderiv_zoomSubst, ite_eq_left rfl, mul_one]
  · intro i _ hi
    rw [pderiv_zoomSubst, ite_eq_right hi, mul_zero]
  · simp

theorem eval_pderiv_zoomLift (t₀ q Z₀ Y₀ : ℝ) (hq : q ≠ 0) (Q : MvPolynomial (Fin 4) ℝ)
    (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point b t) (pderiv 3 (zoomLift t₀ q Z₀ Y₀ Q)) =
      eval (point (zoomCoeff t₀ q Z₀ Y₀ b) (zoomTime t₀ q t)) (pderiv 3 Q) := by
  rw [pderiv_zoomLift, eval_zoomLift t₀ q Z₀ Y₀ hq]

theorem eval_pderiv_pderiv_zoomLift (t₀ q Z₀ Y₀ : ℝ) (hq : q ≠ 0)
    (Q : MvPolynomial (Fin 4) ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point b t) (pderiv 3 (pderiv 3 (zoomLift t₀ q Z₀ Y₀ Q))) =
      eval (point (zoomCoeff t₀ q Z₀ Y₀ b) (zoomTime t₀ q t)) (pderiv 3 (pderiv 3 Q)) := by
  rw [pderiv_zoomLift, pderiv_zoomLift, eval_zoomLift t₀ q Z₀ Y₀ hq]

/-- A fit in the new chart on a time set `I` is the same fit in the old chart on the set of
old times whose new time lies in `I`. -/
theorem zoom_fit_lifts (t₀ q Z₀ Y₀ : ℝ) (hq : q ≠ 0) (Q : MvPolynomial (Fin 4) ℝ)
    (b : Fin 6 → ℝ) (I : Set ℝ) (H c : ℝ)
    (hfit : ∀ t ∈ I, |eval (point (zoomCoeff t₀ q Z₀ Y₀ b) t) Q| ≤ H * c ∧
      |eval (point (zoomCoeff t₀ q Z₀ Y₀ b) t) (pderiv 3 Q)| ≤ H ∧
      |eval (point (zoomCoeff t₀ q Z₀ Y₀ b) t) (pderiv 3 (pderiv 3 Q))| ≤ H / c) :
    ∀ t, zoomTime t₀ q t ∈ I → |eval (point b t) (zoomLift t₀ q Z₀ Y₀ Q)| ≤ H * c ∧
      |eval (point b t) (pderiv 3 (zoomLift t₀ q Z₀ Y₀ Q))| ≤ H ∧
      |eval (point b t) (pderiv 3 (pderiv 3 (zoomLift t₀ q Z₀ Y₀ Q)))| ≤ H / c := by
  intro t ht
  rw [eval_zoomLift t₀ q Z₀ Y₀ hq, eval_pderiv_zoomLift t₀ q Z₀ Y₀ hq,
    eval_pderiv_pderiv_zoomLift t₀ q Z₀ Y₀ hq]
  exact hfit _ ht

/-- The budget bounding the coefficient norms of the zoom substitution. -/
def zoomBudget (t₀ q Z₀ Y₀ : ℝ) : ℝ :=
  1 + (|q⁻¹| + |(q ^ 2)⁻¹|) * (1 + |t₀| + |Z₀| + |Y₀|)

theorem one_le_zoomBudget (t₀ q Z₀ Y₀ : ℝ) : 1 ≤ zoomBudget t₀ q Z₀ Y₀ := by
  have : 0 ≤ (|q⁻¹| + |(q ^ 2)⁻¹|) * (1 + |t₀| + |Z₀| + |Y₀|) := by positivity
  unfold zoomBudget
  linarith

theorem coeffL1_zoomSubst (t₀ q Z₀ Y₀ : ℝ) (i : Fin 4) :
    coeffL1 (zoomSubst t₀ q Z₀ Y₀ i) ≤ zoomBudget t₀ q Z₀ Y₀ := by
  have hA : 0 ≤ |q⁻¹| := abs_nonneg _
  have hB : 0 ≤ |(q ^ 2)⁻¹| := abs_nonneg _
  have ht := abs_nonneg t₀
  have hz := abs_nonneg Z₀
  have hy := abs_nonneg Y₀
  have hb := one_le_zoomBudget t₀ q Z₀ Y₀
  fin_cases i
  · change coeffL1 (C q⁻¹ * (X 0 - C t₀) : MvPolynomial (Fin 4) ℝ) ≤ _
    calc
      _ ≤ |q⁻¹| * coeffL1 (X 0 - C t₀ : MvPolynomial (Fin 4) ℝ) := coeffL1_C_mul_le _ _
      _ ≤ |q⁻¹| * (coeffL1 (X (0 : Fin 4)) + coeffL1 (C t₀ : MvPolynomial (Fin 4) ℝ)) := by
        gcongr; exact coeffL1_sub_le _ _
      _ = |q⁻¹| * (1 + |t₀|) := by rw [coeffL1_X, coeffL1_C]
      _ ≤ _ := by unfold zoomBudget; nlinarith
  · change coeffL1 (C q⁻¹ * (X 1 - C Z₀) : MvPolynomial (Fin 4) ℝ) ≤ _
    calc
      _ ≤ |q⁻¹| * coeffL1 (X 1 - C Z₀ : MvPolynomial (Fin 4) ℝ) := coeffL1_C_mul_le _ _
      _ ≤ |q⁻¹| * (coeffL1 (X (1 : Fin 4)) + coeffL1 (C Z₀ : MvPolynomial (Fin 4) ℝ)) := by
        gcongr; exact coeffL1_sub_le _ _
      _ = |q⁻¹| * (1 + |Z₀|) := by rw [coeffL1_X, coeffL1_C]
      _ ≤ _ := by unfold zoomBudget; nlinarith
  · change coeffL1 (C (q ^ 2)⁻¹ * (X 2 - C Y₀ + C Z₀ * X 0 - C t₀ * X 1) :
      MvPolynomial (Fin 4) ℝ) ≤ _
    have h1 : coeffL1 (X 2 - C Y₀ + C Z₀ * X 0 - C t₀ * X 1 : MvPolynomial (Fin 4) ℝ) ≤
        1 + |Y₀| + |Z₀| + |t₀| := by
      have e1 := coeffL1_sub_le (X 2 - C Y₀ + C Z₀ * X 0 : MvPolynomial (Fin 4) ℝ)
        (C t₀ * X 1)
      have e2 := coeffL1_add_le (X 2 - C Y₀ : MvPolynomial (Fin 4) ℝ) (C Z₀ * X 0)
      have e3 := coeffL1_sub_le (X (2 : Fin 4) : MvPolynomial (Fin 4) ℝ) (C Y₀)
      have e4 := coeffL1_C_mul_le Z₀ (X (0 : Fin 4) : MvPolynomial (Fin 4) ℝ)
      have e5 := coeffL1_C_mul_le t₀ (X (1 : Fin 4) : MvPolynomial (Fin 4) ℝ)
      rw [coeffL1_X] at e3 e4 e5
      rw [coeffL1_C] at e3
      linarith
    calc
      _ ≤ |(q ^ 2)⁻¹| * coeffL1 (X 2 - C Y₀ + C Z₀ * X 0 - C t₀ * X 1 :
          MvPolynomial (Fin 4) ℝ) := coeffL1_C_mul_le _ _
      _ ≤ |(q ^ 2)⁻¹| * (1 + |Y₀| + |Z₀| + |t₀|) := mul_le_mul_of_nonneg_left h1 hB
      _ ≤ _ := by unfold zoomBudget; nlinarith
  · change coeffL1 (X (3 : Fin 4) : MvPolynomial (Fin 4) ℝ) ≤ _
    rw [coeffL1_X]
    exact hb

theorem coeffL1_zoomLift_le (t₀ q Z₀ Y₀ : ℝ) (Q : MvPolynomial (Fin 4) ℝ)
    (hQ : Q.totalDegree ≤ 2) :
    coeffL1 (zoomLift t₀ q Z₀ Y₀ Q) ≤ coeffL1 Q * zoomBudget t₀ q Z₀ Y₀ ^ 2 := by
  have hb := coeffL1_bind₁_le (zoomSubst t₀ q Z₀ Y₀) (zoomBudget t₀ q Z₀ Y₀)
    (one_le_zoomBudget t₀ q Z₀ Y₀) (coeffL1_zoomSubst t₀ q Z₀ Y₀) Q
  exact hb.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (one_le_zoomBudget t₀ q Z₀ Y₀) hQ) (coeffL1_nonneg Q))

end

end Submission.Lib.K4QuadraticSheetCore
