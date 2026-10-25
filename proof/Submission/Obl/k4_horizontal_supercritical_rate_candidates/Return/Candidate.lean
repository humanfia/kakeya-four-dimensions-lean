import Submission.Lib.K4ChartLifting.PolyAlgebra

/-!
# The returned candidate polynomial

`X3 - L(X0, X1, X2) - a₀ P((X0 - t₀)/q, (X1 - Zc)/q)`: the coarse affine fit plus the
block-normalized quadratic produced by Scalar. Degree two, hidden derivative one.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MvPolynomial
open Submission.Lib.K4ChartLifting

noncomputable section

/-- Block normalization of time and first position. -/
def candSubst (t₀ q Zc : ℝ) : Fin 2 → MvPolynomial (Fin 4) ℝ :=
  ![C q⁻¹ * (X 0 - C t₀), C q⁻¹ * (X 1 - C Zc)]

/-- The candidate. -/
def candPoly (L : Fin 4 → ℝ) (a₀ t₀ q Zc : ℝ) (P : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial (Fin 4) ℝ :=
  X 3 - (C (L 0) + C (L 1) * X 0 + C (L 2) * X 1 + C (L 3) * X 2) -
    C a₀ * bind₁ (candSubst t₀ q Zc) P

theorem candSubst_degree (t₀ q Zc : ℝ) (i : Fin 2) : (candSubst t₀ q Zc i).totalDegree ≤ 1 := by
  fin_cases i
  · change (C q⁻¹ * (X (0 : Fin 4) - C t₀)).totalDegree ≤ 1
    refine (totalDegree_mul _ _).trans ?_
    simp only [totalDegree_C, zero_add]
    exact (totalDegree_sub _ _).trans (by simp)
  · change (C q⁻¹ * (X (1 : Fin 4) - C Zc)).totalDegree ≤ 1
    refine (totalDegree_mul _ _).trans ?_
    simp only [totalDegree_C, zero_add]
    exact (totalDegree_sub _ _).trans (by simp)

theorem eval_candPoly (L : Fin 4 → ℝ) (a₀ t₀ q Zc : ℝ) (P : MvPolynomial (Fin 2) ℝ)
    (x : Fin 4 → ℝ) :
    eval x (candPoly L a₀ t₀ q Zc P) =
      x 3 - (L 0 + L 1 * x 0 + L 2 * x 1 + L 3 * x 2) -
        a₀ * eval ![(x 0 - t₀) / q, (x 1 - Zc) / q] P := by
  have hsub : eval x (bind₁ (candSubst t₀ q Zc) P) =
      eval (fun i => eval x (candSubst t₀ q Zc i)) P := eval₂Hom_bind₁ _ _ _ _
  have hargs : (fun i => eval x (candSubst t₀ q Zc i)) = ![(x 0 - t₀) / q, (x 1 - Zc) / q] := by
    funext i
    fin_cases i <;> simp [candSubst, div_eq_inv_mul]
  simp only [candPoly, map_sub, map_add, map_mul, eval_X, eval_C, hsub, hargs]

theorem candPoly_totalDegree (L : Fin 4 → ℝ) (a₀ t₀ q Zc : ℝ) (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) : (candPoly L a₀ t₀ q Zc P).totalDegree ≤ 2 := by
  unfold candPoly
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_sub _ _).trans (max_le (by simp) ?_)
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
        exact (totalDegree_mul _ _).trans (by simp)
      · exact (totalDegree_mul _ _).trans (by simp)
    · exact (totalDegree_mul _ _).trans (by simp)
  · refine (totalDegree_mul _ _).trans ?_
    simp only [totalDegree_C, zero_add]
    exact (totalDegree_bind₁_le_of_le_one _ (candSubst_degree t₀ q Zc) P).trans hP

theorem pderiv_three_candSubst (t₀ q Zc : ℝ) (j : Fin 2) :
    pderiv (3 : Fin 4) (candSubst t₀ q Zc j) = 0 := by
  fin_cases j <;> simp [candSubst, pderiv_X]

theorem pderiv_candPoly (L : Fin 4 → ℝ) (a₀ t₀ q Zc : ℝ) (P : MvPolynomial (Fin 2) ℝ) :
    pderiv (3 : Fin 4) (candPoly L a₀ t₀ q Zc P) = 1 := by
  have hb : pderiv (3 : Fin 4) (bind₁ (candSubst t₀ q Zc) P) = 0 := by
    rw [pderiv_bind₁]
    simp [pderiv_three_candSubst]
  simp [candPoly, hb, pderiv_X]

theorem coeffL1_candSubst_le (t₀ q Zc : ℝ) (i : Fin 2) :
    coeffL1 (candSubst t₀ q Zc i) ≤ 1 + |q⁻¹| * (1 + |t₀| + |Zc|) := by
  have hb : ∀ (k : Fin 4) (c : ℝ), coeffL1 (C q⁻¹ * (X k - C c)) ≤ |q⁻¹| * (1 + |c|) := by
    intro k c
    refine (coeffL1_C_mul_le _ _).trans ?_
    gcongr
    refine (coeffL1_sub_le _ _).trans ?_
    rw [coeffL1_X, coeffL1_C]
  fin_cases i
  · change coeffL1 (C q⁻¹ * (X (0 : Fin 4) - C t₀)) ≤ _
    refine (hb 0 t₀).trans ?_
    have : |q⁻¹| * (1 + |t₀|) ≤ |q⁻¹| * (1 + |t₀| + |Zc|) :=
      mul_le_mul_of_nonneg_left (by linarith [abs_nonneg Zc]) (abs_nonneg _)
    linarith
  · change coeffL1 (C q⁻¹ * (X (1 : Fin 4) - C Zc)) ≤ _
    refine (hb 1 Zc).trans ?_
    have : |q⁻¹| * (1 + |Zc|) ≤ |q⁻¹| * (1 + |t₀| + |Zc|) :=
      mul_le_mul_of_nonneg_left (by linarith [abs_nonneg t₀]) (abs_nonneg _)
    linarith

theorem coeff_candPoly_le (L : Fin 4 → ℝ) (a₀ t₀ q Zc : ℝ) (P : MvPolynomial (Fin 2) ℝ)
    (hP : P.totalDegree ≤ 2) (m : Fin 4 →₀ ℕ) :
    |(candPoly L a₀ t₀ q Zc P).coeff m| ≤
      1 + (|L 0| + |L 1| + |L 2| + |L 3|) +
        |a₀| * (coeffL1 P * (1 + |q⁻¹| * (1 + |t₀| + |Zc|)) ^ 2) := by
  have hS : 1 ≤ 1 + |q⁻¹| * (1 + |t₀| + |Zc|) := le_add_of_nonneg_right (by positivity)
  have hbind := coeffL1_bind₁_le (candSubst t₀ q Zc) _ hS (coeffL1_candSubst_le t₀ q Zc) P
  have hpow : (1 + |q⁻¹| * (1 + |t₀| + |Zc|)) ^ P.totalDegree ≤
      (1 + |q⁻¹| * (1 + |t₀| + |Zc|)) ^ 2 := pow_le_pow_right₀ hS hP
  have haff : coeffL1 (C (L 0) + C (L 1) * X (0 : Fin 4) + C (L 2) * X (1 : Fin 4) +
      C (L 3) * X (2 : Fin 4)) ≤ |L 0| + |L 1| + |L 2| + |L 3| := by
    have h1 := coeffL1_C_mul_le (L 1) (X (0 : Fin 4))
    have h2 := coeffL1_C_mul_le (L 2) (X (1 : Fin 4))
    have h3 := coeffL1_C_mul_le (L 3) (X (2 : Fin 4))
    simp only [coeffL1_X, mul_one] at h1 h2 h3
    refine (coeffL1_add_le _ _).trans ?_
    refine add_le_add ((coeffL1_add_le _ _).trans (add_le_add ((coeffL1_add_le _ _).trans
      (add_le_add (by rw [coeffL1_C]) h1)) h2)) h3
  refine (abs_coeff_le_coeffL1 _ m).trans ?_
  unfold candPoly
  refine (coeffL1_sub_le _ _).trans (add_le_add ((coeffL1_sub_le _ _).trans
    (add_le_add (by rw [coeffL1_X]) haff)) ?_)
  refine (coeffL1_C_mul_le _ _).trans ?_
  gcongr
  exact hbind.trans (mul_le_mul_of_nonneg_left hpow (coeffL1_nonneg _))

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
