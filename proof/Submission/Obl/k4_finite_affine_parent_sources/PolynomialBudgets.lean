-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.ParentFrameInv
import Submission.Obl.k4_remainder_pure_profile_normalization.Normalization.Sizes

namespace Submission.Obl.k4_finite_affine_parent_sources

open MvPolynomial
open Submission.Obl.k4_remainder_pure_profile_normalization.Normalization

noncomputable section

namespace PFrame

/-- The hidden-unit change adds one scalar to the accepted affine
substitution budget. -/
def substBudget (Φ : PFrame) : ℝ := max Φ.F.substBound |Φ.sc|

def unsubstBudget (Φ : PFrame) : ℝ := max Φ.F.unsubstBound |Φ.sc⁻¹|

lemma one_le_substBudget (Φ : PFrame) : 1 ≤ Φ.substBudget :=
  Φ.F.one_le_substBound.trans (le_max_left _ _)

lemma one_le_unsubstBudget (Φ : PFrame) : 1 ≤ Φ.unsubstBudget :=
  Φ.F.one_le_unsubstBound.trans (le_max_left _ _)

lemma coeffL1_subst'_le (Φ : PFrame) (i : Fin 4) :
    coeffL1 (Φ.subst' i) ≤ Φ.substBudget := by
  fin_cases i
  · exact (Φ.F.coeffL1_subst_le 0).trans (le_max_left _ _)
  · exact (Φ.F.coeffL1_subst_le 1).trans (le_max_left _ _)
  · exact (Φ.F.coeffL1_subst_le 2).trans (le_max_left _ _)
  · apply (coeffL1_C_mul_le Φ.sc (X (3 : Fin 4))).trans
    rw [coeffL1_X, mul_one]
    exact le_max_right _ _

lemma coeffL1_isubst_le (Φ : PFrame) (i : Fin 4) :
    coeffL1 (Φ.isubst i) ≤ Φ.unsubstBudget := by
  have heq : ∀ i : Fin 4, i ≠ 3 → Φ.isubst i = Φ.F.unsubst i := by
    intro i hi
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact (hi rfl).elim
  by_cases hi : i = 3
  · subst i
    change coeffL1 (C Φ.sc⁻¹ * X (3 : Fin 4)) ≤ max Φ.F.unsubstBound |Φ.sc⁻¹|
    apply (coeffL1_C_mul_le Φ.sc⁻¹ (X (3 : Fin 4))).trans
    rw [coeffL1_X, mul_one]
    exact le_max_right _ _
  · rw [heq i hi]
    exact (Φ.F.coeffL1_unsubst_le i).trans (le_max_left _ _)

/-- A normalized original test has one explicit coefficient-norm budget,
valid independently of every future candidate loss. -/
theorem coeffL1_normTest_le (Φ : PFrame) (δ : ℝ) (Q : MvPolynomial (Fin 4) ℝ) :
    coeffL1 (Φ.normTest δ Q) ≤
      |δ⁻¹| * (coeffL1 Q * Φ.unsubstBudget ^ Q.totalDegree) := by
  unfold normTest
  apply (coeffL1_smul _ _).trans
  exact mul_le_mul_of_nonneg_left
    (coeffL1_bind₁_le Φ.isubst Φ.unsubstBudget Φ.one_le_unsubstBudget Φ.coeffL1_isubst_le Q)
    (abs_nonneg _)

theorem coeffL1_liftE_le (Φ : PFrame) (δ : ℝ) (Q : MvPolynomial (Fin 4) ℝ) :
    coeffL1 (Φ.liftE δ Q) ≤ |δ| * (coeffL1 Q * Φ.substBudget ^ Q.totalDegree) := by
  unfold liftE
  apply (coeffL1_smul _ _).trans
  exact mul_le_mul_of_nonneg_left
    (coeffL1_bind₁_le Φ.subst' Φ.substBudget Φ.one_le_substBudget Φ.coeffL1_subst'_le Q)
    (abs_nonneg _)

/-- The 81-monomial degree box converts the frozen candidate's
coefficient ceiling into an explicit ORIGINAL-coordinate ceiling. -/
theorem coeff_liftE_quadratic_le
    (Φ : PFrame) (δ : ℝ) (Q : MvPolynomial (Fin 4) ℝ) (hQ : Q.totalDegree ≤ 2)
    (H : ℝ) (hcoeff : ∀ e, |Q.coeff e| ≤ H) (e : Fin 4 →₀ ℕ) :
    |(Φ.liftE δ Q).coeff e| ≤ 81 * |δ| * H * Φ.substBudget ^ 2 := by
  have hL : coeffL1 Q ≤ 81 * H := by
    simpa using coeffL1_le_of_coeff_le Q hQ H hcoeff
  have hpow : Φ.substBudget ^ Q.totalDegree ≤ Φ.substBudget ^ 2 :=
    pow_le_pow_right₀ Φ.one_le_substBudget hQ
  calc
    _ ≤ coeffL1 (Φ.liftE δ Q) := abs_coeff_le_coeffL1 _ _
    _ ≤ |δ| * (coeffL1 Q * Φ.substBudget ^ Q.totalDegree) := Φ.coeffL1_liftE_le δ Q
    _ ≤ |δ| * (coeffL1 Q * Φ.substBudget ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (coeffL1_nonneg Q)) (abs_nonneg δ)
    _ ≤ |δ| * ((81 * H) * Φ.substBudget ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL (sq_nonneg _)) (abs_nonneg δ)
    _ = 81 * |δ| * H * Φ.substBudget ^ 2 := by ring

end PFrame

end

end Submission.Obl.k4_finite_affine_parent_sources
