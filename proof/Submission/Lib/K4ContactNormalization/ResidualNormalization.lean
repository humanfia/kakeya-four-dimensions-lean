import Submission.Lib.K4ContactNormalization.RowNormalization

/-! Adapted from: here:o200 (session x0696). -/

/-! Exact algebra for subtracting an affine hidden sheet. Coefficient bounds
in this file keep their dependence on that sheet explicit. -/

namespace Submission.Lib.K4ContactNormalization

open MvPolynomial
open Submission.Lib.K4ChartLifting

noncomputable section

def affineBase (L : Fin 4 → ℝ) : MvPolynomial (Fin 4) ℝ :=
  C (L 0) + C (L 1) * X 0 + C (L 2) * X 1 + C (L 3) * X 2

/-- The residual remains affine along each trajectory. -/
def residualCoeff (L : Fin 4 → ℝ) (a : ℝ) (b : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![b 0, b 1, (b 2 - L 0 - L 2 * b 0 - L 3 * b 1) / a,
    b 3, b 4, (b 5 - L 1 - L 2 * b 3 - L 3 * b 4) / a]

def residualSubst (L : Fin 4 → ℝ) (a : ℝ) : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![X 0, X 1, X 2, C a⁻¹ * (X 3 - affineBase L)]

def residualLift (L : Fin 4 → ℝ) (a : ℝ) (Q : MvPolynomial (Fin 4) ℝ) :
    MvPolynomial (Fin 4) ℝ := C a * bind₁ (residualSubst L a) Q

theorem affineBase_degree (L : Fin 4 → ℝ) : (affineBase L).totalDegree ≤ 1 :=
  deg1_add (deg1_add (deg1_add (deg1_C _) (deg1_C_mul _ (deg1_X _)))
    (deg1_C_mul _ (deg1_X _))) (deg1_C_mul _ (deg1_X _))

theorem residualSubst_degree (L : Fin 4 → ℝ) (a : ℝ) (i : Fin 4) :
    (residualSubst L a i).totalDegree ≤ 1 := by
  fin_cases i
  · exact deg1_X _
  · exact deg1_X _
  · exact deg1_X _
  · exact deg1_C_mul _ (deg1_sub (deg1_X _) (affineBase_degree L))

theorem residualLift_degree (L : Fin 4 → ℝ) (a : ℝ) (Q : MvPolynomial (Fin 4) ℝ) :
    (residualLift L a Q).totalDegree ≤ Q.totalDegree := by
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  exact totalDegree_bind₁_le_of_le_one _ (residualSubst_degree L a) Q

theorem eval_residualSubst (L : Fin 4 → ℝ) (a : ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    (fun i => eval (point b t) (residualSubst L a i)) = point (residualCoeff L a b) t := by
  funext i
  fin_cases i <;> simp [point, residualSubst, residualCoeff, affineBase, div_eq_mul_inv]
  ring

/-- Only the hidden substitution has a hidden derivative, and it is the
constant inverse residual scale. -/
theorem pderiv_residualSubst (L : Fin 4 → ℝ) (a : ℝ) (i : Fin 4) :
    pderiv (3 : Fin 4) (residualSubst L a i) = if i = 3 then C a⁻¹ else 0 := by
  fin_cases i <;> simp [residualSubst, affineBase, pderiv_X]

theorem pderiv_residual_pullback (L : Fin 4 → ℝ) (a : ℝ)
    (Q : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (bind₁ (residualSubst L a) Q) =
      C a⁻¹ * bind₁ (residualSubst L a) (pderiv 3 Q) := by
  rw [pderiv_bind₁, Finset.sum_eq_single (3 : Fin 4)]
  · rw [pderiv_residualSubst, ite_eq_left rfl, mul_comm]
  · intro i _ hi
    rw [pderiv_residualSubst, ite_eq_right hi, mul_zero]
  · simp

theorem pderiv_residualLift (L : Fin 4 → ℝ) {a : ℝ} (ha : a ≠ 0)
    (Q : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (residualLift L a Q) = bind₁ (residualSubst L a) (pderiv 3 Q) := by
  rw [residualLift, Derivation.leibniz]
  simp only [pderiv_C, smul_eq_mul, mul_zero, add_zero, pderiv_residual_pullback]
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]

theorem second_pderiv_residualLift (L : Fin 4 → ℝ) {a : ℝ} (ha : a ≠ 0)
    (Q : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (pderiv 3 (residualLift L a Q)) =
      C a⁻¹ * bind₁ (residualSubst L a) (pderiv 3 (pderiv 3 Q)) := by
  rw [pderiv_residualLift L ha, pderiv_residual_pullback]

theorem eval_residualLift (L : Fin 4 → ℝ) (a : ℝ) (Q : MvPolynomial (Fin 4) ℝ)
    (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point b t) (residualLift L a Q) = a * eval (point (residualCoeff L a b) t) Q := by
  rw [residualLift, eval_mul, eval_C, eval_bind₁', eval_residualSubst]

theorem eval_pderiv_residualLift (L : Fin 4 → ℝ) {a : ℝ} (ha : a ≠ 0)
    (Q : MvPolynomial (Fin 4) ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point b t) (pderiv 3 (residualLift L a Q)) =
      eval (point (residualCoeff L a b) t) (pderiv 3 Q) := by
  rw [pderiv_residualLift L ha, eval_bind₁', eval_residualSubst]

theorem eval_second_pderiv_residualLift (L : Fin 4 → ℝ) {a : ℝ} (ha : a ≠ 0)
    (Q : MvPolynomial (Fin 4) ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    eval (point b t) (pderiv 3 (pderiv 3 (residualLift L a Q))) =
      a⁻¹ * eval (point (residualCoeff L a b) t) (pderiv 3 (pderiv 3 Q)) := by
  rw [second_pderiv_residualLift L ha, eval_mul, eval_C, eval_bind₁', eval_residualSubst]

/-- Full-block fits lift at the product thickness, while the first hidden
derivative stays in the original derivative units. -/
theorem residual_fit_lifts (L : Fin 4 → ℝ) {a : ℝ} (ha : 0 < a)
    (Q : MvPolynomial (Fin 4) ℝ) (b : Fin 6 → ℝ) (I : Set ℝ) (H c : ℝ)
    (hfit : ∀ t ∈ I, |eval (point (residualCoeff L a b) t) Q| ≤ H * c ∧
      |eval (point (residualCoeff L a b) t) (pderiv 3 Q)| ≤ H ∧
      |eval (point (residualCoeff L a b) t) (pderiv 3 (pderiv 3 Q))| ≤ H / c) :
    ∀ t ∈ I, |eval (point b t) (residualLift L a Q)| ≤ H * (a * c) ∧
      |eval (point b t) (pderiv 3 (residualLift L a Q))| ≤ H ∧
      |eval (point b t) (pderiv 3 (pderiv 3 (residualLift L a Q)))| ≤ H / (a * c) := by
  intro t ht
  obtain ⟨hv, hd, hdd⟩ := hfit t ht
  rw [eval_residualLift, eval_pderiv_residualLift L ha.ne', eval_second_pderiv_residualLift L ha.ne']
  refine ⟨?_, hd, ?_⟩
  · rw [abs_mul, abs_of_pos ha]
    convert mul_le_mul_of_nonneg_left hv ha.le using 1 <;> ring
  · rw [abs_mul, abs_of_pos (inv_pos.mpr ha)]
    convert mul_le_mul_of_nonneg_left hdd (inv_pos.mpr ha).le using 1 <;> field_simp <;> ring

theorem coeffL1_affineBase (L : Fin 4 → ℝ) :
    coeffL1 (affineBase L) ≤ |L 0| + |L 1| + |L 2| + |L 3| := by
  have h1 := coeffL1_C_mul_le (L 1) (X (0 : Fin 4))
  have h2 := coeffL1_C_mul_le (L 2) (X (1 : Fin 4))
  have h3 := coeffL1_C_mul_le (L 3) (X (2 : Fin 4))
  simp only [coeffL1_X, mul_one] at h1 h2 h3
  have ha := coeffL1_add_le (C (L 0) : MvPolynomial (Fin 4) ℝ) (C (L 1) * X 0)
  have hb := coeffL1_add_le (C (L 0) + C (L 1) * X 0 : MvPolynomial (Fin 4) ℝ) (C (L 2) * X 1)
  have hc := coeffL1_add_le
    (C (L 0) + C (L 1) * X 0 + C (L 2) * X 1 : MvPolynomial (Fin 4) ℝ) (C (L 3) * X 2)
  rw [coeffL1_C] at ha
  dsimp only [affineBase]
  linarith

/-- This bound explicitly includes the affine part. It must not be mistaken
for the homogeneous coefficient estimate in the final candidate principle. -/
def residualBudget (L : Fin 4 → ℝ) (a : ℝ) : ℝ :=
  1 + |a⁻¹| * (1 + (|L 0| + |L 1| + |L 2| + |L 3|))

theorem one_le_residualBudget (L : Fin 4 → ℝ) (a : ℝ) : 1 ≤ residualBudget L a := by
  have hh : 0 ≤ |a⁻¹| * (1 + (|L 0| + |L 1| + |L 2| + |L 3|)) := by positivity
  dsimp only [residualBudget]
  linarith

theorem coeffL1_residualSubst (L : Fin 4 → ℝ) (a : ℝ) (i : Fin 4) :
    coeffL1 (residualSubst L a i) ≤ residualBudget L a := by
  fin_cases i
  · exact (coeffL1_X _).le.trans (one_le_residualBudget L a)
  · exact (coeffL1_X _).le.trans (one_le_residualBudget L a)
  · exact (coeffL1_X _).le.trans (one_le_residualBudget L a)
  · calc
      _ ≤ |a⁻¹| * coeffL1 (X 3 - affineBase L) := coeffL1_C_mul_le _ _
      _ ≤ |a⁻¹| * (coeffL1 (X (3 : Fin 4)) + coeffL1 (affineBase L)) := by
        gcongr; exact coeffL1_sub_le _ _
      _ ≤ |a⁻¹| * (1 + (|L 0| + |L 1| + |L 2| + |L 3|)) := by
        rw [coeffL1_X]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (coeffL1_affineBase L)) (abs_nonneg _)
      _ ≤ residualBudget L a := by dsimp only [residualBudget]; linarith

theorem coeff_residualLift_le (L : Fin 4 → ℝ) (a : ℝ)
    (Q : MvPolynomial (Fin 4) ℝ) (hQ : Q.totalDegree ≤ 2) (e : Fin 4 →₀ ℕ) :
    |(residualLift L a Q).coeff e| ≤ |a| * coeffL1 Q * residualBudget L a ^ 2 := by
  apply (abs_coeff_le_coeffL1 _ _).trans
  apply (coeffL1_C_mul_le _ _).trans
  have hb := coeffL1_bind₁_le (residualSubst L a) (residualBudget L a)
    (one_le_residualBudget L a) (coeffL1_residualSubst L a) Q
  calc
    _ ≤ |a| * (coeffL1 Q * residualBudget L a ^ Q.totalDegree) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ ≤ |a| * (coeffL1 Q * residualBudget L a ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_residualBudget L a) hQ)
          (coeffL1_nonneg Q)) (abs_nonneg _)
    _ = _ := by ring

end
end Submission.Lib.K4ContactNormalization
