-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.ChartAxes
import Submission.Lib.K4FinitePlankAtlases.PlankFrame
import Submission.Lib.K4ChartLifting.Bounds
import Submission.Lib.K4XInterface.Charts
import Submission.Obl.k4_finite_affine_parent_sources.RelativeRowGeometry

namespace Submission.Obl.k4_finite_affine_parent_sources.MajorFrame

open Submission.Obl.k4_compatible_pair_frame_preparation.Construction
open Submission.Lib.K4FinitePlankAtlases
open Submission.Lib.K4XInterface

noncomputable section

/-- The unit tangent of the actual longest column. -/
def tangent (Q : Matrix (Fin 2) (Fin 2) ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (r₁ Q)⁻¹ • longCol Q

/-- An orthogonal frame at the actual major and minor scales. Its Jacobian
is exactly the old absolute determinant; no spectral decomposition is needed. -/
def frame (Q : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  plankFrame (r₁ Q) (r₂ Q) (tangent Q) (nrm Q)

lemma minor_pos {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) : 0 < r₂ Q :=
  div_pos (abs_pos.mpr hQ) (r₁_pos hQ)

lemma norm_tangent {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) : ‖tangent Q‖ = 1 := by
  dsimp only [tangent]
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (r₁_nonneg Q))]
  change (r₁ Q)⁻¹ * r₁ Q = 1
  exact inv_mul_cancel₀ (r₁_pos hQ).ne'

lemma tangent_orthogonal (Q : Matrix (Fin 2) (Fin 2) ℝ) : inner ℝ (tangent Q) (nrm Q) = 0 := by
  simp only [tangent, inner_smul_left, inner_longCol_nrm, conj_trivial, mul_zero]

lemma abs_det {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) : |(frame Q).det| = |Q.det| := by
  rw [frame, plankFrame_abs_det (r₁_pos hQ) (minor_pos hQ) (norm_tangent hQ)
    (norm_nrm hQ) (tangent_orthogonal Q)]
  dsimp only [r₂]
  field_simp [(r₁_pos hQ).ne']

lemma det_ne_zero {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) : (frame Q).det ≠ 0 := by
  have h := abs_det hQ
  exact abs_ne_zero.mp (by rw [h]; exact abs_ne_zero.mpr hQ)

lemma inverse_action {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (z : EuclideanSpace ℝ (Fin 2)) :
    Matrix.toEuclideanLin (frame Q)⁻¹ z =
      WithLp.toLp 2 ![inner ℝ z (tangent Q) / r₁ Q, inner ℝ z (nrm Q) / r₂ Q] :=
  plankFrame_inverse_action (r₁_pos hQ).ne' (minor_pos hQ).ne'
    (norm_tangent hQ) (norm_nrm hQ) (tangent_orthogonal Q) z

/-- The first inverse row has only the reciprocal MAJOR scale. This is
the exact bound needed to transport the original planar velocity code. -/
lemma inverse_major_row {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) (e : Fin 2) :
    (frame Q)⁻¹ 0 e = tangent Q e / r₁ Q := by
  rw [frame, plankFrame_inverse (r₁_pos hQ).ne' (minor_pos hQ).ne'
    (norm_tangent hQ) (norm_nrm hQ) (tangent_orthogonal Q)]
  fin_cases e <;> rfl

/-- Replacing the old frame by this major frame costs a factor of three
in whole-block geometry, even at arbitrarily large aspect ratio. -/
lemma inverse_comp_bound {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (w : EuclideanSpace ℝ (Fin 2)) :
    ‖Matrix.toEuclideanLin (frame Q)⁻¹ (Matrix.toEuclideanLin Q w)‖ ≤ 3 * ‖w‖ := by
  have h₀ : |inner ℝ (Matrix.toEuclideanLin Q w) (tangent Q) / r₁ Q| ≤ 2 * ‖w‖ := by
    rw [abs_div, abs_of_pos (r₁_pos hQ), div_le_iff₀ (r₁_pos hQ)]
    exact (abs_real_inner_le_norm _ _).trans
      (by simpa only [norm_tangent hQ, mul_one] using norm_toEuclideanLin_le Q w)
  have h₁ : |inner ℝ (Matrix.toEuclideanLin Q w) (nrm Q) / r₂ Q| ≤ ‖w‖ := by
    rw [abs_div, abs_of_pos (minor_pos hQ), div_le_iff₀ (minor_pos hQ)]
    exact abs_inner_nrm_le hQ w
  rw [inverse_action hQ]
  have h := Submission.Lib.K4ChartLifting.plane_norm_le
    (WithLp.toLp 2 ![inner ℝ (Matrix.toEuclideanLin Q w) (tangent Q) / r₁ Q,
      inner ℝ (Matrix.toEuclideanLin Q w) (nrm Q) / r₂ Q])
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using
    h.trans ((add_le_add h₀ h₁).trans_eq (by ring))

lemma fit {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (z : EuclideanSpace ℝ (Fin 2)) (κ : ℝ)
    (hz : ‖Matrix.toEuclideanLin Q⁻¹ z‖ ≤ κ) :
    ‖Matrix.toEuclideanLin (frame Q)⁻¹ z‖ ≤ 3 * κ := by
  have h := inverse_comp_bound hQ (Matrix.toEuclideanLin Q⁻¹ z)
  rw [toEuclideanLin_inv_cancel Q hQ] at h
  exact h.trans (mul_le_mul_of_nonneg_left hz (by norm_num))

lemma entries_le {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) :
    (∑ i : Fin 2, ∑ j : Fin 2, |frame Q i j|) ≤
      4 * (∑ i : Fin 2, ∑ j : Fin 2, |Q i j|) := by
  have h := plankFrame_entries (r₁_pos hQ) (minor_pos hQ) (norm_tangent hQ) (norm_nrm hQ)
  exact h.trans (by linarith [r₂_le_r₁ hQ, r₁_le_entrySum Q])

lemma inverse_entries_le {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) :
    (∑ i : Fin 2, ∑ j : Fin 2, |(frame Q)⁻¹ i j|) ≤
      4 * (∑ i : Fin 2, ∑ j : Fin 2, |Q⁻¹ i j|) := by
  have h := plankFrame_inverse_entries (r₁_pos hQ) (minor_pos hQ)
    (norm_tangent hQ) (norm_nrm hQ) (tangent_orthogonal Q)
  have hi : (r₁ Q)⁻¹ ≤ (r₂ Q)⁻¹ := inv_anti₀ (minor_pos hQ) (r₂_le_r₁ hQ)
  have hsmall : (r₂ Q)⁻¹ ≤ ∑ i : Fin 2, ∑ j : Fin 2, |Q⁻¹ i j| := by
    rw [sum_abs_inv_fin2]
    dsimp only [r₂]
    rw [inv_div]
    exact div_le_div_of_nonneg_right (r₁_le_entrySum Q) (abs_nonneg _)
  exact h.trans (by linarith)

/-- Apply cumulative largest-axis fullness to the actual relative child
matrix in this parent frame. No relative angular-alignment assumption
is used: the small parent-minor term is the only quantity to absorb. -/
lemma relative_major_lower
    (Q₀ Q₁ : Matrix (Fin 2) (Fin 2) ℝ) (hQ₀ : Q₀.det ≠ 0) (full : ℝ)
    (hfull : full ≤ r₁ Q₁)
    (hminor : r₂ Q₀ * ‖frameRow ((frame Q₀)⁻¹ * Q₁) 1‖ ≤ full / 2) :
    full / (2 * r₁ Q₀) ≤ ‖frameRow ((frame Q₀)⁻¹ * Q₁) 0‖ := by
  let M := (frame Q₀)⁻¹ * Q₁
  have hprod : frame Q₀ * M = Q₁ := by
    rw [show frame Q₀ * M = (frame Q₀ * (frame Q₀)⁻¹) * Q₁ by
      dsimp only [M]; rw [Matrix.mul_assoc]]
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (det_ne_zero hQ₀)), Matrix.one_mul]
  apply relative_major_row_lower (r₁ Q₀) (r₂ Q₀) full (r₁_pos hQ₀)
    (r₂_nonneg Q₀) (tangent Q₀) (nrm Q₀) (norm_tangent hQ₀) (norm_nrm hQ₀) M
    _ hminor
  change ∃ j : Fin 2, full ≤ ‖WithLp.toLp 2 (fun i => (frame Q₀ * M) i j)‖
  rw [hprod]
  by_cases hcol : ‖col1 Q₁‖ ≤ ‖col0 Q₁‖
  · refine ⟨0, ?_⟩
    have heq : WithLp.toLp 2 (fun i => Q₁ i 0) = col0 Q₁ := by
      ext i; fin_cases i <;> rfl
    rw [heq]
    simpa only [r₁, longCol, ite_eq_left hcol] using hfull
  · refine ⟨1, ?_⟩
    have heq : WithLp.toLp 2 (fun i => Q₁ i 1) = col1 Q₁ := by
      ext i; fin_cases i <;> rfl
    rw [heq]
    simpa only [r₁, longCol, ite_eq_right hcol] using hfull

end

end Submission.Obl.k4_finite_affine_parent_sources.MajorFrame
