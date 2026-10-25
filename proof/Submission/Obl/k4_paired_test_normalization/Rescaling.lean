-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/Rescaling.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_paired_test_normalization.Interface
import Submission.Obl.k4_quadratic_atlas_normalization.Curvature

namespace Submission.Obl.k4_paired_test_normalization

open MvPolynomial

/-- Scaling an equation scales its frozen discriminant by the square factor. -/
theorem disc_C_mul (P : MvPolynomial (Fin 4) ℝ) (t : ℝ) :
    disc (C t * P) = C (t ^ 2) * disc P := by
  simp only [disc, pderiv_C_mul, map_sub, map_mul, map_pow, map_ofNat, eval₂Hom_C]
  ring

theorem abs_disc_coeff_C_mul (P : MvPolynomial (Fin 4) ℝ) (t : ℝ) (m : Fin 3 →₀ ℕ) :
    |(disc (C t * P)).coeff m| = t ^ 2 * |(disc P).coeff m| := by
  rw [disc_C_mul, coeff_C_mul, abs_mul, abs_of_nonneg (sq_nonneg t)]

/-- Positive downward equation scaling preserves the hidden-curvature ceiling. -/
theorem curvature_ceiling_C_mul (P : MvPolynomial (Fin 4) ℝ) {t A : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hA : |eval (0 : Fin 4 → ℝ) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤ A) :
    |eval (0 : Fin 4 → ℝ) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (C t * P)))| ≤ A := by
  rw [pderiv_C_mul, pderiv_C_mul, eval_mul, eval_C, abs_mul, abs_of_nonneg ht]
  exact (mul_le_of_le_one_left (abs_nonneg _) ht1).trans hA

theorem totalDegree_C_mul_le (P : MvPolynomial (Fin 4) ℝ) (t : ℝ) :
    (C t * P).totalDegree ≤ P.totalDegree := by
  simpa only [totalDegree_C, zero_add] using totalDegree_mul (C t) P

theorem abs_coeff_C_mul_le (P : MvPolynomial (Fin 4) ℝ) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (m : Fin 4 →₀ ℕ) :
    |(C t * P).coeff m| ≤ |P.coeff m| := by
  rw [coeff_C_mul, abs_mul, abs_of_nonneg ht]
  exact mul_le_of_le_one_left (abs_nonneg _) ht1

theorem curvature_C_mul (P : MvPolynomial (Fin 4) ℝ) (t : ℝ) :
    Submission.Obl.k4_quadratic_atlas_normalization.curvature (C t * P) (3 : Fin 4) =
      t * Submission.Obl.k4_quadratic_atlas_normalization.curvature P (3 : Fin 4) := by
  simp only [Submission.Obl.k4_quadratic_atlas_normalization.curvature,
    pderiv_C_mul, coeff_C_mul]

theorem abs_eval_C_mul_le (P : MvPolynomial (Fin 4) ℝ) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (z : Fin 4 → ℝ) :
    |eval z (C t * P)| ≤ |eval z P| := by
  rw [eval_mul, eval_C, abs_mul, abs_of_nonneg ht]
  exact mul_le_of_le_one_left (abs_nonneg _) ht1

/-- The small curvature/residual cross term improves under downward scaling,
even when a larger residual ceiling is used for the affine replacements. -/
theorem curvature_value_ceiling_C_mul (P : MvPolynomial (Fin 4) ℝ) {t A : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (z : Fin 4 → ℝ)
    (hA : 2 * |Submission.Obl.k4_quadratic_atlas_normalization.curvature P (3 : Fin 4) *
      eval z P| ≤ A) :
    2 * |Submission.Obl.k4_quadratic_atlas_normalization.curvature (C t * P) (3 : Fin 4) *
      eval z (C t * P)| ≤ A := by
  rw [curvature_C_mul, eval_mul, eval_C]
  have heq : 2 * |t * Submission.Obl.k4_quadratic_atlas_normalization.curvature P (3 : Fin 4) *
      (t * eval z P)| = t ^ 2 *
        (2 * |Submission.Obl.k4_quadratic_atlas_normalization.curvature P (3 : Fin 4) * eval z P|) := by
    simp only [abs_mul, abs_of_nonneg ht]
    ring
  rw [heq]
  exact (mul_le_of_le_one_left (by positivity) (pow_le_one₀ ht ht1)).trans hA

/-- A positive rescaling preserves the very same simple sheet, hence every
source proximity, matching and trajectory-fit bound for it. -/
theorem simple_root_C_mul (P : MvPolynomial (Fin 4) ℝ) {t : ℝ} (ht : t ≠ 0)
    (F : EuclideanSpace ℂ (Fin 3) → ℂ) (U : Set (EuclideanSpace ℂ (Fin 3)))
    (hroot : ∀ z ∈ U,
      eval (Fin.snoc (fun i : Fin 3 => z i) (F z)) (P.map (algebraMap ℝ ℂ)) = 0 ∧
      eval (Fin.snoc (fun i : Fin 3 => z i) (F z))
        ((pderiv (3 : Fin 4) P).map (algebraMap ℝ ℂ)) ≠ 0) :
    ∀ z ∈ U,
      eval (Fin.snoc (fun i : Fin 3 => z i) (F z)) ((C t * P).map (algebraMap ℝ ℂ)) = 0 ∧
      eval (Fin.snoc (fun i : Fin 3 => z i) (F z))
        ((pderiv (3 : Fin 4) (C t * P)).map (algebraMap ℝ ℂ)) ≠ 0 := by
  intro z hz
  obtain ⟨hzero, hne⟩ := hroot z hz
  simp only [map_mul, map_C, eval_C, pderiv_C_mul, Complex.coe_algebraMap]
  exact ⟨by rw [hzero, mul_zero], mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) hne⟩

end Submission.Obl.k4_paired_test_normalization
