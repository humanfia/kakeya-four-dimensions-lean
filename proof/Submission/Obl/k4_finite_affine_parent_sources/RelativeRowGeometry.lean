-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Lib.K4FinitePlankAtlases.PlankFrame
import Submission.Lib.K4XInterface.Charts

namespace Submission.Obl.k4_finite_affine_parent_sources

open Submission.Lib.K4FinitePlankAtlases Submission.Lib.K4XInterface

noncomputable section

def frameRow (M : Matrix (Fin 2) (Fin 2) ℝ) (e : Fin 2) :
    EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun f => M e f)

lemma frameRow_norm_sq (M : Matrix (Fin 2) (Fin 2) ℝ) (e : Fin 2) :
    ‖frameRow M e‖ ^ 2 = M e 0 ^ 2 + M e 1 ^ 2 := norm_sq_fin2 _

lemma frameRow_pos {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det ≠ 0) :
    0 < ‖frameRow M 0‖ := by
  by_contra h
  have hz : frameRow M 0 = 0 := norm_eq_zero.mp (le_antisymm (le_of_not_gt h) (norm_nonneg _))
  have h₀ : M 0 0 = 0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hz
  have h₁ : M 0 1 = 0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hz
  apply hM
  rw [Matrix.det_fin_two, h₀, h₁]
  ring

lemma plankFrame_action (a b : ℝ) (e n w : EuclideanSpace ℝ (Fin 2)) :
    Matrix.toEuclideanLin (plankFrame a b e n) w = (a * w 0) • e + (b * w 1) • n := by
  ext j
  fin_cases j <;> simp [plankFrame, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- Each physical column is controlled by the two relative rows and the
actual major and minor widths of its parent frame. -/
lemma relative_column_bound
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (e n : EuclideanSpace ℝ (Fin 2)) (he : ‖e‖ = 1) (hn : ‖n‖ = 1)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) :
    ‖WithLp.toLp 2 (fun i => (plankFrame a b e n * M) i j)‖ ≤
      a * ‖frameRow M 0‖ + b * ‖frameRow M 1‖ := by
  have hcol : WithLp.toLp 2 (fun i => (plankFrame a b e n * M) i j) =
      (a * M 0 j) • e + (b * M 1 j) • n := by
    ext i
    fin_cases i <;> simp [plankFrame, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have h₀ : |M 0 j| ≤ ‖frameRow M 0‖ := by
    simpa only [frameRow, Real.norm_eq_abs] using PiLp.norm_apply_le (frameRow M 0) j
  have h₁ : |M 1 j| ≤ ‖frameRow M 1‖ := by
    simpa only [frameRow, Real.norm_eq_abs] using PiLp.norm_apply_le (frameRow M 1) j
  rw [hcol]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, he, hn,
    mul_one, mul_one, abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  exact add_le_add (mul_le_mul_of_nonneg_left h₀ ha) (mul_le_mul_of_nonneg_left h₁ hb)

/-- Cumulative physical fullness forces a lower bound on the relative
major row once the parent's minor contribution is absorbed. -/
theorem relative_major_row_lower
    (a b full : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (e n : EuclideanSpace ℝ (Fin 2)) (he : ‖e‖ = 1) (hn : ‖n‖ = 1)
    (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hfull : ∃ j : Fin 2,
      full ≤ ‖WithLp.toLp 2 (fun i => (plankFrame a b e n * M) i j)‖)
    (hminor : b * ‖frameRow M 1‖ ≤ full / 2) :
    full / (2 * a) ≤ ‖frameRow M 0‖ := by
  obtain ⟨j, hj⟩ := hfull
  have h := hj.trans (relative_column_bound a b ha.le hb e n he hn M j)
  rw [div_le_iff₀ (by positivity : 0 < 2 * a)]
  linarith

lemma tilt_le_row_ratio (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hrow : 0 < ‖frameRow M 0‖) :
    |(M 1 0 * M 0 0 + M 1 1 * M 0 1) /
      (M 0 0 ^ 2 + M 0 1 ^ 2)| ≤ ‖frameRow M 1‖ / ‖frameRow M 0‖ := by
  have heq : M 1 0 * M 0 0 + M 1 1 * M 0 1 =
      inner ℝ (frameRow M 1) (frameRow M 0) := by
    simp [frameRow, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]
  rw [heq, ← frameRow_norm_sq M 0, abs_div, abs_of_pos (sq_pos_of_pos hrow)]
  apply (div_le_div_of_nonneg_right (abs_real_inner_le_norm _ _) (sq_nonneg _)).trans_eq
  field_simp

lemma tilt_le_of_row_bounds (M : Matrix (Fin 2) (Fin 2) ℝ)
    (lower upper : ℝ) (hlower : 0 < lower)
    (hlo : lower ≤ ‖frameRow M 0‖) (hup : ‖frameRow M 1‖ ≤ upper) :
    |(M 1 0 * M 0 0 + M 1 1 * M 0 1) /
      (M 0 0 ^ 2 + M 0 1 ^ 2)| ≤ upper / lower := by
  apply (tilt_le_row_ratio M (hlower.trans_le hlo)).trans
  exact div_le_div₀ ((norm_nonneg _).trans hup) hup hlower hlo

lemma minor_scale_eq (M : Matrix (Fin 2) (Fin 2) ℝ) :
    Real.sqrt (M.det ^ 2 / (M 0 0 ^ 2 + M 0 1 ^ 2)) =
      |M.det| / ‖frameRow M 0‖ := by
  rw [← frameRow_norm_sq M 0, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs,
    Real.sqrt_sq (norm_nonneg _)]

lemma minor_scale_le (M : Matrix (Fin 2) (Fin 2) ℝ)
    (lower upper : ℝ) (hlower : 0 < lower)
    (hlo : lower ≤ ‖frameRow M 0‖) (hdet : |M.det| ≤ upper) :
    Real.sqrt (M.det ^ 2 / (M 0 0 ^ 2 + M 0 1 ^ 2)) ≤ upper / lower := by
  rw [minor_scale_eq]
  exact div_le_div₀ ((abs_nonneg _).trans hdet) hdet hlower hlo

end

end Submission.Obl.k4_finite_affine_parent_sources
