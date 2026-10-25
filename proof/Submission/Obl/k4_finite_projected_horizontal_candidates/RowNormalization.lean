import Mathlib
import Submission.Lib.K4ChartLifting.Normalize

/-!
Algebraic part of the row-to-horizontal reduction in Section 8. The error is
measured in the original incidence law; these identities require no change of
prior or normalization of retained mass.
-/

namespace Submission.Obl.k4_finite_projected_horizontal_candidates

open MvPolynomial

noncomputable section

/-- The four coordinates in the frozen prepared-parent model. -/
def point (b : Fin 6 → ℝ) (t : ℝ) : Fin 4 → ℝ :=
  ![t, b 0 + t * b 3, b 1 + t * b 4, b 2 + t * b 5]

/-- Subtract the fitted constant row and divide the transverse coordinate by
its nonzero skew coefficient. -/
def skewCoeff (B : Fin 2 → ℝ) (lam : ℝ) (b : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![b 0, (b 1 - B 1 * b 0) / lam, b 2, b 3,
    (b 4 - B 0 - B 1 * b 3) / lam, b 5]

/-- The cancellation of the two skew terms along an affine trajectory. -/
theorem skew_row_identity (B T : Fin 2 → ℝ) (lam b v H t : ℝ) :
    H - B 0 - v * B 1 + lam * b =
      (H - (T 0 + v * T 1)) +
        (T 0 - B 0 + lam * (b + t * v)) + v * (T 1 - B 1 - lam * t) := by
  ring

/-- A pointwise row fit gives a time-independent equation on the trajectory. -/
theorem row_fit_equation {B T : Fin 2 → ℝ} {lam b v H t D E : ℝ}
    (hH : |H - (T 0 + v * T 1)| ≤ D)
    (hT0 : |T 0 - B 0 + lam * (b + t * v)| ≤ E)
    (hT1 : |T 1 - B 1 - lam * t| ≤ E) :
    |H - B 0 - v * B 1 + lam * b| ≤ D + (1 + |v|) * E := by
  rw [skew_row_identity B T lam b v H t]
  calc
    |(H - (T 0 + v * T 1)) + (T 0 - B 0 + lam * (b + t * v)) +
        v * (T 1 - B 1 - lam * t)|
        ≤ (|H - (T 0 + v * T 1)| + |T 0 - B 0 + lam * (b + t * v)|) +
          |v| * |T 1 - B 1 - lam * t| := by
            calc
              _ ≤ |(H - (T 0 + v * T 1)) + (T 0 - B 0 + lam * (b + t * v))| +
                    |v * (T 1 - B 1 - lam * t)| := abs_add_le _ _
              _ ≤ (|H - (T 0 + v * T 1)| + |T 0 - B 0 + lam * (b + t * v)|) +
                    |v * (T 1 - B 1 - lam * t)| := add_le_add (abs_add_le _ _) le_rfl
              _ = _ := by rw [abs_mul]
    _ ≤ (D + E) + |v| * E :=
      add_le_add (add_le_add hH hT0) (mul_le_mul_of_nonneg_left hT1 (abs_nonneg _))
    _ = D + (1 + |v|) * E := by ring

/-- A small skew coefficient gives the original velocity strip. -/
theorem strip_of_small_skew {B : Fin 2 → ℝ} {lam b v H R delta K : ℝ}
    (hrow : |H - B 0 - v * B 1 + lam * b| ≤ R)
    (hlam : |lam| ≤ delta) (hb : |b| ≤ K) :
    |H - B 0 - v * B 1| ≤ R + delta * K := by
  calc
    |H - B 0 - v * B 1| = |(H - B 0 - v * B 1 + lam * b) - lam * b| := by ring_nf
    _ ≤ |H - B 0 - v * B 1 + lam * b| + |lam * b| := abs_sub _ _
    _ ≤ R + delta * K := by
      rw [abs_mul]
      exact add_le_add hrow (mul_le_mul hlam hb (abs_nonneg _) ((abs_nonneg _).trans hlam))

/-- Dividing by a nonzero skew coefficient produces the horizontal equation. -/
theorem horizontal_error (B : Fin 2 → ℝ) {lam : ℝ} (hlam : lam ≠ 0)
    (b : Fin 6 → ℝ) :
    |skewCoeff B lam b 4 + skewCoeff B lam b 0| =
      |b 4 - B 0 - b 3 * B 1 + lam * b 0| / |lam| := by
  change |(b 4 - B 0 - B 1 * b 3) / lam + b 0| = _
  rw [show (b 4 - B 0 - B 1 * b 3) / lam + b 0 =
      (b 4 - B 0 - b 3 * B 1 + lam * b 0) / lam by field_simp]
  exact abs_div _ _

/-- The quantitative alternatives use the same row fit and do not discard mass. -/
theorem row_fit_alternative {B T : Fin 2 → ℝ} {lam b v H t D E delta K : ℝ}
    (hdelta : 0 < delta) (hb : |b| ≤ K)
    (hH : |H - (T 0 + v * T 1)| ≤ D)
    (hT0 : |T 0 - B 0 + lam * (b + t * v)| ≤ E)
    (hT1 : |T 1 - B 1 - lam * t| ≤ E) :
    |H - B 0 - v * B 1| ≤ D + (1 + |v|) * E + delta * K ∨
      (lam ≠ 0 ∧ |(H - B 0 - v * B 1) / lam + b| ≤
        (D + (1 + |v|) * E) / delta) := by
  have hr := row_fit_equation hH hT0 hT1
  by_cases hl : |lam| ≤ delta
  · exact Or.inl (strip_of_small_skew hr hl hb)
  · have hdl : delta < |lam| := lt_of_not_ge hl
    have hl0 : lam ≠ 0 := abs_pos.mp (hdelta.trans hdl)
    refine Or.inr ⟨hl0, ?_⟩
    have heq : (H - B 0 - v * B 1) / lam + b =
        (H - B 0 - v * B 1 + lam * b) / lam := by field_simp
    rw [heq, abs_div]
    exact (div_le_div_of_nonneg_right hr (abs_nonneg _)).trans
      (div_le_div_of_nonneg_left ((abs_nonneg _).trans hr) hdelta hdl.le)

/-- The forward affine coordinate substitution. It leaves the hidden variable fixed. -/
def skewSubst (B : Fin 2 → ℝ) (lam : ℝ) : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![X 0, X 1, C lam⁻¹ * (X 2 - C (B 0) * X 0 - C (B 1) * X 1), X 3]

/-- The inverse affine coordinate substitution. -/
def unskewSubst (B : Fin 2 → ℝ) (lam : ℝ) : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![X 0, X 1, C lam * X 2 + C (B 0) * X 0 + C (B 1) * X 1, X 3]

theorem eval_skewSubst (B : Fin 2 → ℝ) (lam : ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    (fun i => eval (point b t) (skewSubst B lam i)) = point (skewCoeff B lam b) t := by
  funext i
  fin_cases i <;> simp [skewSubst, point, skewCoeff, div_eq_mul_inv] <;> ring

theorem eval_unskewSubst (B : Fin 2 → ℝ) {lam : ℝ} (hlam : lam ≠ 0)
    (b : Fin 6 → ℝ) (t : ℝ) :
    (fun i => eval (point (skewCoeff B lam b) t) (unskewSubst B lam i)) = point b t := by
  funext i
  fin_cases i <;> simp [unskewSubst, point, skewCoeff] <;> field_simp <;> ring


open Submission.Lib.K4ChartLifting

theorem degree_skewSubst (B : Fin 2 → ℝ) (lam : ℝ) (i : Fin 4) :
    (skewSubst B lam i).totalDegree ≤ 1 := by
  fin_cases i
  · exact deg1_X _
  · exact deg1_X _
  · exact deg1_C_mul _ (deg1_sub (deg1_sub (deg1_X _)
      (deg1_C_mul _ (deg1_X _))) (deg1_C_mul _ (deg1_X _)))
  · exact deg1_X _

theorem degree_unskewSubst (B : Fin 2 → ℝ) (lam : ℝ) (i : Fin 4) :
    (unskewSubst B lam i).totalDegree ≤ 1 := by
  fin_cases i
  · exact deg1_X _
  · exact deg1_X _
  · exact deg1_add (deg1_add (deg1_C_mul _ (deg1_X _))
      (deg1_C_mul _ (deg1_X _))) (deg1_C_mul _ (deg1_X _))
  · exact deg1_X _

/-- Pulling a polynomial back along the row normalization preserves degree. -/
theorem degree_skew_pullback (B : Fin 2 → ℝ) (lam : ℝ) (Q : MvPolynomial (Fin 4) ℝ) :
    (bind₁ (skewSubst B lam) Q).totalDegree ≤ Q.totalDegree :=
  totalDegree_bind₁_le_of_le_one _ (degree_skewSubst B lam) Q

theorem degree_unskew_pullback (B : Fin 2 → ℝ) (lam : ℝ) (Q : MvPolynomial (Fin 4) ℝ) :
    (bind₁ (unskewSubst B lam) Q).totalDegree ≤ Q.totalDegree :=
  totalDegree_bind₁_le_of_le_one _ (degree_unskewSubst B lam) Q

/-- Row normalization keeps the hidden derivative in the same units. -/
theorem pderiv_skew_pullback (B : Fin 2 → ℝ) (lam : ℝ) (Q : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (bind₁ (skewSubst B lam) Q) =
      bind₁ (skewSubst B lam) (pderiv 3 Q) := by
  apply pderiv_bind₁_of_diagonal
  · simp [skewSubst]
  · intro j hj
    fin_cases j <;> simp_all [skewSubst, pderiv_X]

theorem pderiv_unskew_pullback (B : Fin 2 → ℝ) (lam : ℝ) (Q : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (bind₁ (unskewSubst B lam) Q) =
      bind₁ (unskewSubst B lam) (pderiv 3 Q) := by
  apply pderiv_bind₁_of_diagonal
  · simp [unskewSubst]
  · intro j hj
    fin_cases j <;> simp_all [unskewSubst, pderiv_X]

theorem eval_skew_pullback (B : Fin 2 → ℝ) (lam : ℝ) (Q : MvPolynomial (Fin 4) ℝ)
    (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point b t) (bind₁ (skewSubst B lam) Q) =
      eval (point (skewCoeff B lam b) t) Q := by
  rw [eval_bind₁', eval_skewSubst]

theorem eval_unskew_pullback (B : Fin 2 → ℝ) {lam : ℝ} (hlam : lam ≠ 0)
    (Q : MvPolynomial (Fin 4) ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point (skewCoeff B lam b) t) (bind₁ (unskewSubst B lam) Q) =
      eval (point b t) Q := by
  rw [eval_bind₁', eval_unskewSubst B hlam]

/-- A whole-block candidate and both hidden derivative bounds pull back without
an additional error factor. -/
theorem skew_fit_iff (B : Fin 2 → ℝ) (lam : ℝ) (Q : MvPolynomial (Fin 4) ℝ)
    (b : Fin 6 → ℝ) (I : Set ℝ) (H a : ℝ) :
    (∀ t ∈ I, |eval (point b t) (bind₁ (skewSubst B lam) Q)| ≤ H * a ∧
      |eval (point b t) (pderiv 3 (bind₁ (skewSubst B lam) Q))| ≤ H ∧
      |eval (point b t) (pderiv 3 (pderiv 3 (bind₁ (skewSubst B lam) Q)))| ≤ H / a) ↔
    (∀ t ∈ I, |eval (point (skewCoeff B lam b) t) Q| ≤ H * a ∧
      |eval (point (skewCoeff B lam b) t) (pderiv 3 Q)| ≤ H ∧
      |eval (point (skewCoeff B lam b) t) (pderiv 3 (pderiv 3 Q))| ≤ H / a) := by
  simp only [pderiv_skew_pullback, eval_skew_pullback]

/-- A coefficient budget for the affine normalization. -/
def skewBudget (B : Fin 2 → ℝ) (lam : ℝ) : ℝ :=
  1 + |lam⁻¹| * (1 + |B 0| + |B 1|)

theorem one_le_skewBudget (B : Fin 2 → ℝ) (lam : ℝ) : 1 ≤ skewBudget B lam := by
  dsimp [skewBudget]
  have hp : 0 ≤ |lam⁻¹| * (1 + |B 0| + |B 1|) := by positivity
  linarith

theorem coeffL1_skewSubst (B : Fin 2 → ℝ) (lam : ℝ) (i : Fin 4) :
    coeffL1 (skewSubst B lam i) ≤ skewBudget B lam := by
  fin_cases i
  · simpa [skewSubst, coeffL1_X] using one_le_skewBudget B lam
  · simpa [skewSubst, coeffL1_X] using one_le_skewBudget B lam
  · change coeffL1 (C lam⁻¹ * (X 2 - C (B 0) * X 0 - C (B 1) * X 1)) ≤ _
    have hinner : coeffL1 (X 2 - C (B 0) * X 0 - C (B 1) * X 1 :
        MvPolynomial (Fin 4) ℝ) ≤ 1 + |B 0| + |B 1| := by
      calc
        _ ≤ coeffL1 (X 2 - C (B 0) * X 0 : MvPolynomial (Fin 4) ℝ) +
              coeffL1 (C (B 1) * X 1 : MvPolynomial (Fin 4) ℝ) := coeffL1_sub_le _ _
        _ ≤ (coeffL1 (X 2 : MvPolynomial (Fin 4) ℝ) +
              coeffL1 (C (B 0) * X 0 : MvPolynomial (Fin 4) ℝ)) +
              coeffL1 (C (B 1) * X 1 : MvPolynomial (Fin 4) ℝ) :=
                add_le_add (coeffL1_sub_le _ _) le_rfl
        _ ≤ 1 + |B 0| * 1 + |B 1| * 1 := by
          rw [coeffL1_X]
          exact add_le_add (add_le_add le_rfl (by
            simpa only [coeffL1_X] using coeffL1_C_mul_le (B 0) (X (0 : Fin 4))))
              (by simpa only [coeffL1_X] using coeffL1_C_mul_le (B 1) (X (1 : Fin 4)))
        _ = _ := by ring
    calc
      _ ≤ |lam⁻¹| * coeffL1 (X 2 - C (B 0) * X 0 - C (B 1) * X 1 :
            MvPolynomial (Fin 4) ℝ) := coeffL1_C_mul_le _ _
      _ ≤ |lam⁻¹| * (1 + |B 0| + |B 1|) :=
        mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
      _ ≤ skewBudget B lam := by unfold skewBudget; linarith
  · simpa [skewSubst, coeffL1_X] using one_le_skewBudget B lam

/-- Coefficient growth is at most quadratic in the row-normalization budget. -/
theorem coeff_skew_pullback_le (B : Fin 2 → ℝ) (lam : ℝ)
    (Q : MvPolynomial (Fin 4) ℝ) (hQ : Q.totalDegree ≤ 2) (e : Fin 4 →₀ ℕ) :
    |(bind₁ (skewSubst B lam) Q).coeff e| ≤ coeffL1 Q * skewBudget B lam ^ 2 := by
  apply (abs_coeff_le_coeffL1 _ _).trans
  apply (coeffL1_bind₁_le _ _ (one_le_skewBudget B lam) (coeffL1_skewSubst B lam) Q).trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_skewBudget B lam) hQ)
    (coeffL1_nonneg Q)

end
end Submission.Obl.k4_finite_projected_horizontal_candidates
