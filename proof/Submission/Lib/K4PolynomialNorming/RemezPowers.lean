/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.MvPolynomialRemez

open Set MeasureTheory MvPolynomial

namespace Submission.Lib.K4PolynomialNorming

theorem degree_factor_le_power (A : ℝ) (hA : 2 ≤ A) (D : ℕ) :
    ((D + 1 : ℕ) : ℝ) ≤ A ^ D := by
  have hA0 : 0 ≤ A := by linarith
  induction D with
  | zero => norm_num
  | succ D ih =>
      have hD0 : (0 : ℝ) ≤ D := by positivity
      calc
        ((D + 1 + 1 : ℕ) : ℝ) ≤ 2 * ((D + 1 : ℕ) : ℝ) := by push_cast; linarith
        _ ≤ 2 * A ^ D := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ ≤ A * A ^ D := mul_le_mul_of_nonneg_right hA (pow_nonneg hA0 _)
        _ = A ^ (D + 1) := by rw [pow_succ]; ring

private theorem remez_base_le_power (A : ℝ) (hA : 2 ≤ A) (D : ℕ) :
    1 + 128 * (D + 1 : ℕ) / A⁻¹ ≤ A ^ (D + 10) := by
  have hA0 : 0 ≤ A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have h128 : (128 : ℝ) ≤ A ^ 7 :=
    (show (128 : ℝ) ≤ 2 ^ 7 by norm_num).trans (pow_le_pow_left₀ (by norm_num) hA 7)
  have hdegree := degree_factor_le_power A hA D
  have hlarge : 1 ≤ A ^ (D + 8) := one_le_pow₀ hA1
  calc
    _ = 1 + 128 * (D + 1 : ℕ) * A := by simp only [div_eq_mul_inv, inv_inv]
    _ ≤ 1 + A ^ 7 * A ^ D * A := by gcongr
    _ = 1 + A ^ (D + 8) := by rw [pow_add]; ring
    _ ≤ 2 * A ^ (D + 8) := by linarith
    _ ≤ A * A ^ (D + 8) := mul_le_mul_of_nonneg_right hA (pow_nonneg hA0 _)
    _ = A ^ (D + 9) := by rw [show D + 9 = (D + 8) + 1 by omega, pow_succ]; ring
    _ ≤ A ^ (D + 10) := pow_le_pow_right₀ hA1 (by omega)

/-- Absorb the explicit Remez constant into a single fixed power when the
observation-set volume has a reciprocal-power lower bound. -/
theorem remez_loss_le_power (A : ℝ) (hA : 2 ≤ A) (D n : ℕ)
    (c ε : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 128) (hε : 0 ≤ ε) :
    (1 + c * (D + 1 : ℕ) / A⁻¹) ^ (n * D) * ε ≤ A ^ (n * D * (D + 10)) * ε := by
  have hA0 : 0 ≤ A := by linarith
  have hbase : 1 + c * (D + 1 : ℕ) / A⁻¹ ≤ A ^ (D + 10) := by
    apply le_trans _ (remez_base_le_power A hA D)
    gcongr
  calc
    _ ≤ (A ^ (D + 10)) ^ (n * D) * ε := by gcongr
    _ = _ := by rw [← pow_mul, mul_comm (D + 10) (n * D)]

/-- Binary real polynomial norming in the single-power form used for
subpower bookkeeping. -/
theorem real_binary_polynomial_coeff_le_power
    (F : MvPolynomial (Fin 2) ℝ) (D : ℕ) (hD : F.totalDegree ≤ D)
    (E : Set (EuclideanSpace ℝ (Fin 2))) (hE : MeasurableSet E)
    (hbox : ∀ u ∈ E, ∀ i, |u i| ≤ 1)
    (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 ≤ ε) (hmass : ENNReal.ofReal A⁻¹ ≤ volume E)
    (hsmall : ∀ u ∈ E, |MvPolynomial.eval (fun i => u i) F| ≤ ε) :
    ∀ m : Fin 2 →₀ ℕ, |F.coeff m| ≤ A ^ (2 * D * (D + 10)) * ε := by
  have h := real_euclidean_binary_mvPolynomial_coeff_le_of_small_values F D hD E hE hbox
    A⁻¹ ε (inv_pos.mpr (by linarith)) hε hmass hsmall
  intro m
  exact (h m).trans (remez_loss_le_power A hA D 2 32 ε (by norm_num) (by norm_num) hε)

/-- Ternary real polynomial norming in the single-power form used for
subpower bookkeeping. -/
theorem real_ternary_polynomial_coeff_le_power
    (F : MvPolynomial (Fin 3) ℝ) (D : ℕ) (hD : F.totalDegree ≤ D)
    (E : Set (EuclideanSpace ℝ (Fin 3))) (hE : MeasurableSet E)
    (hbox : ∀ u ∈ E, ∀ i, |u i| ≤ 1)
    (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 ≤ ε) (hmass : ENNReal.ofReal A⁻¹ ≤ volume E)
    (hsmall : ∀ u ∈ E, |MvPolynomial.eval (fun i => u i) F| ≤ ε) :
    ∀ m : Fin 3 →₀ ℕ, |F.coeff m| ≤ A ^ (3 * D * (D + 10)) * ε := by
  have h := real_euclidean_ternary_mvPolynomial_coeff_le_of_small_values F D hD E hE hbox
    A⁻¹ ε (inv_pos.mpr (by linarith)) hε hmass hsmall
  intro m
  exact (h m).trans (remez_loss_le_power A hA D 3 128 ε (by norm_num) le_rfl hε)

/-- A common Mathlib-only norming interface for the two base dimensions in
the Kakeya argument. The exponent depends only on the fixed polynomial degree. -/
theorem low_dimensional_polynomial_norming : ∀ D : ℕ, ∃ C : ℕ, 1 ≤ C ∧
    ∀ n : ℕ, (n = 2 ∨ n = 3) → ∀ (F : MvPolynomial (Fin n) ℝ), F.totalDegree ≤ D →
      ∀ E : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet E →
        (∀ u ∈ E, ∀ i, |u i| ≤ 1) → ∀ A ε : ℝ, 2 ≤ A → 0 ≤ ε →
          ENNReal.ofReal A⁻¹ ≤ volume E →
            (∀ u ∈ E, |MvPolynomial.eval (fun i => u i) F| ≤ ε) →
              ∀ m : Fin n →₀ ℕ, |F.coeff m| ≤ A ^ C * ε := by
  intro D
  refine ⟨3 * D * (D + 10) + 1, by omega, ?_⟩
  intro n hn
  rcases hn with rfl | rfl
  · intro F hD E hE hbox A ε hA hε hmass hsmall m
    have h := real_binary_polynomial_coeff_le_power F D hD E hE hbox A ε hA hε hmass hsmall m
    exact h.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by linarith : 1 ≤ A) (by nlinarith)) hε)
  · intro F hD E hE hbox A ε hA hε hmass hsmall m
    have h := real_ternary_polynomial_coeff_le_power F D hD E hE hbox A ε hA hε hmass hsmall m
    exact h.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by linarith : 1 ≤ A) (Nat.le_succ _)) hε)

end Submission.Lib.K4PolynomialNorming
