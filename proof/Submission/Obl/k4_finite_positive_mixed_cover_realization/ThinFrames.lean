/- Adapted from this LOT tree: o199, session x0695, branch x0695,
   commit 9136fa89, Submission/Obl/k4_finite_path_candidate_conversion/ThinFrames.lean.
   This file retains the source's own provenance comments below. -/
import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripGeometry
import Submission.Obl.k4_mk_finite_duality.Tuple

/-!
A planar ellipsoid of small determinant has a thin unit-normal direction.
An inverse row with large norm supplies the direction. This avoids selecting
a scalar slope or imposing a lower bound on a chosen physical component.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open Submission.Lib.K4XInterface
open scoped RealInnerProductSpace

def frameRow (M : Frame) (i : Fin 2) : Plane := WithLp.toLp 2 (fun j => M i j)

theorem frameRow_inner (M : Frame) (i : Fin 2) (w : Plane) :
    inner ℝ w (frameRow M i) = (Matrix.toEuclideanLin M w) i := by
  fin_cases i <;> simp [frameRow, PiLp.inner_apply, Fin.sum_univ_two, Matrix.toLpLin_apply]

theorem exists_large_inverse_row (M : Frame) (hM : M.det ≠ 0)
    {a : ℝ} (ha : 0 < a) (hdet : |M.det| ≤ a ^ 2) :
    ∃ i : Fin 2, a⁻¹ ≤ ‖frameRow M⁻¹ i‖ := by
  have hhad := k4_mk_finite_duality.abs_det_rows_le_prod_norm (frameRow M⁻¹)
  have hmat : (Matrix.of fun i j => frameRow M⁻¹ i j) = M⁻¹ := rfl
  rw [hmat, Fin.prod_univ_two, det_inv_fin2, abs_inv] at hhad
  have hlow : a⁻¹ * a⁻¹ ≤ |M.det|⁻¹ := by
    calc
      _ = (a ^ 2)⁻¹ := by simp [pow_two, mul_inv_rev]
      _ ≤ _ := inv_anti₀ (abs_pos.mpr hM) hdet
  by_contra hnone
  push Not at hnone
  have hprod : ‖frameRow M⁻¹ 0‖ * ‖frameRow M⁻¹ 1‖ < a⁻¹ * a⁻¹ :=
    (mul_le_mul_of_nonneg_left (hnone 1).le (norm_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_right (hnone 0) (inv_pos.mpr ha))
  exact (not_lt_of_ge (hlow.trans hhad)) hprod

/-- The ellipsoid `M (ball 0 V)` fits a unit-normal strip of width `a V`
whenever `|det M| <= a²`. -/
theorem exists_thin_frame_normal (M : Frame) (hM : M.det ≠ 0)
    {a : ℝ} (ha : 0 < a) (hdet : |M.det| ≤ a ^ 2) :
    ∃ n : Plane, ‖n‖ = 1 ∧
      ∀ w : Plane, |inner ℝ (Matrix.toEuclideanLin M w) n| ≤ a * ‖w‖ := by
  obtain ⟨i, hi⟩ := exists_large_inverse_row M hM ha hdet
  let row := frameRow M⁻¹ i
  have hrow : 0 < ‖row‖ := (inv_pos.mpr ha).trans_le hi
  have hri : ‖row‖⁻¹ ≤ a := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr ha) hi
  refine ⟨‖row‖⁻¹ • row, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hrow), inv_mul_cancel₀ hrow.ne']
  · intro w
    have hcancel : Matrix.toEuclideanLin M⁻¹ (Matrix.toEuclideanLin M w) = w := by
      rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM)]
      simp
    have hcoord : |w i| ≤ ‖w‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le w i
    calc
      _ = ‖row‖⁻¹ * |w i| := by
        rw [inner_smul_right, abs_mul, abs_of_pos (inv_pos.mpr hrow)]
        change ‖row‖⁻¹ * |inner ℝ (Matrix.toEuclideanLin M w) (frameRow M⁻¹ i)| = _
        rw [frameRow_inner, hcancel]
      _ ≤ a * ‖w‖ := mul_le_mul hri hcoord (abs_nonneg _) ha.le

/-- Translate the thin ellipsoid without changing its unit-normal width.
The bias is a function of the original two chart centers, not of a sampled
trajectory. -/
theorem exists_thin_affine_frame_strip {Ω : Type*} (M : Frame) (hM : M.det ≠ 0)
    (b : Plane) (velocity : Ω → Plane) (S : Set Ω)
    {a V : ℝ} (ha : 0 < a) (hdet : |M.det| ≤ a ^ 2)
    (hfit : ∀ p ∈ S, ∃ w : Plane, ‖w‖ ≤ V ∧ velocity p = b + Matrix.toEuclideanLin M w) :
    ∃ (n : Plane) (β : ℝ), ‖n‖ = 1 ∧
      ∀ p ∈ S, |inner ℝ (velocity p) n - β| ≤ a * V := by
  obtain ⟨n, hn, hthin⟩ := exists_thin_frame_normal M hM ha hdet
  refine ⟨n, inner ℝ b n, hn, ?_⟩
  intro p hp
  obtain ⟨w, hw, heq⟩ := hfit p hp
  rw [heq, inner_add_left, add_sub_cancel_left]
  exact (hthin w).trans (mul_le_mul_of_nonneg_left hw ha.le)

end Submission.Obl.k4_finite_positive_mixed_cover_realization
