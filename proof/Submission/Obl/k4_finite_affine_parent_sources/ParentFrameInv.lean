-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o199, session x0700, commit 711b90f1.
-- Source: Submission/Obl/k4_finite_path_candidate_conversion/ParentFrameInv.lean.
import Submission.Obl.k4_finite_affine_parent_sources.ParentFrame

/-!
# Pushing original tests into the parent's model coordinates

`PFrame.normTest δ R = δ⁻¹ · R ∘ isubst`: evaluation at a normalised graph point is `δ⁻¹` times the
original evaluation, the hidden derivative scales by `sc⁻¹`, and the degree does not grow.
Written by x0700 for o199.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_finite_affine_parent_sources

open MvPolynomial Submission.Lib.K4XInterface
open Submission.Obl.k4_remainder_pure_profile_normalization.Normalization

noncomputable section

namespace PFrame

variable (Φ : PFrame)

theorem eval_isubst (hq : Φ.F.q ≠ 0) (hD : IsUnit Φ.F.D.det) (hsc : Φ.sc ≠ 0)
    (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    (fun i => eval (exS Φ.eb l ((t - Φ.F.t₀) / Φ.F.q)) (Φ.isubst i)) = gx l t := by
  have hp := Φ.F.planarPoint_normTraj hq l t
  have hD' := Frame.toEuclideanLin_mul_inv_apply Φ.F.D hD (planarPoint l t - Φ.F.c - t • Φ.F.u)
  rw [← hp] at hD'
  have h0 := congrArg (fun w : Plane => w 0) hD'
  have h1 := congrArg (fun w : Plane => w 1) hD'
  simp only [toEuclideanLin_apply_fin2] at h0 h1
  simp [planarPoint, Frame.normTraj] at h0 h1
  have ht : Φ.F.t₀ + Φ.F.q * ((t - Φ.F.t₀) / Φ.F.q) = t := by field_simp; ring
  funext i
  fin_cases i
  · simp [isubst, exS, gx]
    linarith
  · simp [isubst, exS, eb, gx]
    rw [ht]
    linarith
  · simp [isubst, exS, eb, gx]
    rw [ht]
    linarith
  · simp [isubst, exS, eb, gx, Frame.normCoeff]
    field_simp
    ring

theorem totalDegree_isubst_le (i : Fin 4) : (Φ.isubst i).totalDegree ≤ 1 := by
  fin_cases i
  · exact deg1_add (deg1_C _) (deg1_C_mul _ (deg1_X _))
  · exact deg1_add (deg1_add (deg1_add (deg1_C _)
      (by
        refine (totalDegree_mul _ _).trans ?_
        have h1 : (C Φ.F.t₀ + C Φ.F.q * X 0 : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 :=
          deg1_add (deg1_C _) (deg1_C_mul _ (deg1_X _))
        have h2 : (C (Φ.F.u 0) : MvPolynomial (Fin 4) ℝ).totalDegree = 0 := totalDegree_C _
        omega)) (deg1_C_mul _ (deg1_X _))) (deg1_C_mul _ (deg1_X _))
  · exact deg1_add (deg1_add (deg1_add (deg1_C _)
      (by
        refine (totalDegree_mul _ _).trans ?_
        have h1 : (C Φ.F.t₀ + C Φ.F.q * X 0 : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 :=
          deg1_add (deg1_C _) (deg1_C_mul _ (deg1_X _))
        have h2 : (C (Φ.F.u 1) : MvPolynomial (Fin 4) ℝ).totalDegree = 0 := totalDegree_C _
        omega)) (deg1_C_mul _ (deg1_X _))) (deg1_C_mul _ (deg1_X _))
  · exact deg1_C_mul _ (deg1_X _)

theorem pderiv_three_isubst (j : Fin 4) :
    pderiv (3 : Fin 4) (Φ.isubst j) = if j = 3 then C Φ.sc⁻¹ else 0 := by
  fin_cases j <;> simp [isubst, pderiv_X]

/-- An original test pushed to model coordinates, divided by `δ`. -/
def normTest (δ : ℝ) (R : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  δ⁻¹ • bind₁ Φ.isubst R

theorem eval_normTest (hq : Φ.F.q ≠ 0) (hD : IsUnit Φ.F.D.det) (hsc : Φ.sc ≠ 0) (δ : ℝ)
    (R : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    eval (exS Φ.eb l ((t - Φ.F.t₀) / Φ.F.q)) (Φ.normTest δ R) = δ⁻¹ * eval (gx l t) R := by
  rw [normTest, smul_eval, eval_bind₁', Φ.eval_isubst hq hD hsc l t]

theorem totalDegree_normTest_le (δ : ℝ) (R : MvPolynomial (Fin 4) ℝ) :
    (Φ.normTest δ R).totalDegree ≤ R.totalDegree :=
  (totalDegree_smul_le _ _).trans (totalDegree_bind₁_le_of_le_one _ Φ.totalDegree_isubst_le R)

theorem pderiv_normTest (δ : ℝ) (R : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (Φ.normTest δ R) = Φ.sc⁻¹ • Φ.normTest δ (pderiv 3 R) := by
  rw [normTest, normTest, Derivation.map_smul, pderiv_bind₁, Fin.sum_univ_four]
  simp only [Φ.pderiv_three_isubst, Fin.isValue, Fin.reduceEq, ite_false, ite_true, mul_zero,
    zero_add]
  simp only [smul_eq_C_mul]
  ring

end PFrame

end

end Submission.Obl.k4_finite_affine_parent_sources
