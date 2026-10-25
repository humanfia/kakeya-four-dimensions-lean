-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.Diagonal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.Width
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.AffineVolume
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Geometry

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (norm_sq_coords)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (affineEquiv_volume)

noncomputable section

def diagonalMap (s : Fin 3 → ℝ) : Space →ₗ[ℝ] Space where
  toFun p := WithLp.toLp 2 (fun i => s i * p i)
  map_add' p q := by ext i; simp; ring
  map_smul' t p := by ext i; simp; ring

@[simp] theorem diagonalMap_apply (s : Fin 3 → ℝ) (p : Space) (i : Fin 3) :
    diagonalMap s p i = s i * p i := rfl

theorem diagonalMap_det (s : Fin 3 → ℝ) :
    LinearMap.det (diagonalMap s) = ∏ i, s i := by
  let B := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have he : LinearMap.toMatrix B B (diagonalMap s) = Matrix.diagonal s := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, B, EuclideanSpace.basisFun_apply,
        OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr, Matrix.diagonal,
        EuclideanSpace.single, diagonalMap]
  rw [← LinearMap.det_toMatrix B, he, Matrix.det_diagonal]

def diagonalEquiv (s : Fin 3 → ℝ) (hs : ∀ i, s i ≠ 0) : Space ≃ₗ[ℝ] Space :=
  (diagonalMap s).equivOfDetNeZero (by rw [diagonalMap_det]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => hs i))

@[simp] theorem diagonalEquiv_apply (s : Fin 3 → ℝ) (hs : ∀ i, s i ≠ 0) (p : Space) :
    diagonalEquiv s hs p = diagonalMap s p := rfl

theorem diagonalEquiv_symm_apply (s : Fin 3 → ℝ) (hs : ∀ i, s i ≠ 0) (p : Space)
    (i : Fin 3) : (diagonalEquiv s hs).symm p i = p i / s i := by
  have hh := congrArg (fun q : Space => q i) ((diagonalEquiv s hs).apply_symm_apply p)
  change s i * (diagonalEquiv s hs).symm p i = p i at hh
  apply (eq_div_iff (hs i)).mpr
  simpa only [mul_comm] using hh

theorem diagonalMap_norm_le {s : Fin 3 → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hs : ∀ i, |s i| ≤ L) (p : Space) : ‖diagonalMap s p‖ ≤ L * ‖p‖ := by
  have hi (i : Fin 3) : (s i * p i) ^ 2 ≤ L ^ 2 * p i ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right
      (sq_le_sq' (abs_le.mp (hs i)).1 (abs_le.mp (hs i)).2) (sq_nonneg _)
  have hn := norm_sq_coords p
  have hm := norm_sq_coords (diagonalMap s p)
  simp only [diagonalMap_apply] at hm
  have hh : ‖diagonalMap s p‖ ^ 2 ≤ (L * ‖p‖) ^ 2 := by
    rw [mul_pow, hn, hm]
    nlinarith only [hi 0, hi 1, hi 2]
  nlinarith only [hh, norm_nonneg (diagonalMap s p), mul_nonneg hL (norm_nonneg p)]

theorem diagonalMap_norm_lower {s : Fin 3 → ℝ} {l : ℝ} (hl : 0 ≤ l)
    (hs : ∀ i, l ≤ |s i|) (p : Space) : l * ‖p‖ ≤ ‖diagonalMap s p‖ := by
  have hi (i : Fin 3) : l ^ 2 * p i ^ 2 ≤ (s i * p i) ^ 2 := by
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith only [hs i, sq_abs (s i), mul_nonneg (sub_nonneg.mpr (hs i))
      (add_nonneg (abs_nonneg (s i)) hl)]
  have hn := norm_sq_coords p
  have hm := norm_sq_coords (diagonalMap s p)
  simp only [diagonalMap_apply] at hm
  have hh : (l * ‖p‖) ^ 2 ≤ ‖diagonalMap s p‖ ^ 2 := by
    rw [mul_pow, hn, hm]
    nlinarith only [hi 0, hi 1, hi 2]
  nlinarith only [hh, norm_nonneg (diagonalMap s p), mul_nonneg hl (norm_nonneg p)]

def coordinateAffine (e : AffineIsometryEquiv ℝ Space Space)
    (s : Fin 3 → ℝ) (hs : ∀ i, s i ≠ 0) : Space ≃ᵃ[ℝ] Space :=
  e.symm.toAffineEquiv.trans (diagonalEquiv s hs).toAffineEquiv

@[simp] theorem coordinateAffine_apply (e : AffineIsometryEquiv ℝ Space Space)
    (s : Fin 3 → ℝ) (hs : ∀ i, s i ≠ 0) (p : Space) :
    coordinateAffine e s hs p = diagonalMap s (e.symm p) := rfl

theorem coordinateAffine_volume (e : AffineIsometryEquiv ℝ Space Space)
    (s : Fin 3 → ℝ) (hs : ∀ i, 0 < s i) (U : Set Space) :
    volume (coordinateAffine e s (fun i => (hs i).ne') '' U) =
      ENNReal.ofReal (∏ i, s i) * volume U := by
  change volume ((fun p => (diagonalEquiv s (fun i => (hs i).ne')).toAffineEquiv (e.symm p)) '' U) = _
  rw [← Set.image_image, affineEquiv_volume,
    WangZahlLot.Obl.wz_frostman_rigid_copies_volume.affine_volume_image]
  change ENNReal.ofReal |LinearMap.det (diagonalMap s)| * volume U = _
  rw [diagonalMap_det, abs_of_pos (Finset.prod_pos (fun i _ => hs i))]

theorem coordinateAffine_dist_upper (e : AffineIsometryEquiv ℝ Space Space)
    {s : Fin 3 → ℝ} (hs : ∀ i, s i ≠ 0) {L : ℝ} (hL : 0 ≤ L)
    (hLs : ∀ i, |s i| ≤ L) (p q : Space) :
    dist (coordinateAffine e s hs p) (coordinateAffine e s hs q) ≤ L * dist p q := by
  simp only [coordinateAffine_apply, dist_eq_norm, ← map_sub]
  simpa only [← dist_eq_norm, e.symm.dist_map] using diagonalMap_norm_le hL hLs (e.symm p - e.symm q)

theorem coordinateAffine_dist_lower (e : AffineIsometryEquiv ℝ Space Space)
    {s : Fin 3 → ℝ} (hs : ∀ i, s i ≠ 0) {l : ℝ} (hl : 0 ≤ l)
    (hls : ∀ i, l ≤ |s i|) (p q : Space) :
    l * dist p q ≤ dist (coordinateAffine e s hs p) (coordinateAffine e s hs q) := by
  simp only [coordinateAffine_apply, dist_eq_norm, ← map_sub]
  simpa only [← dist_eq_norm, e.symm.dist_map] using diagonalMap_norm_lower hl hls (e.symm p - e.symm q)

end
end WangZahlLot.Obl.wz_flat_factored_improvement
