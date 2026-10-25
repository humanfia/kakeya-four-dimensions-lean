/-
Adapted from: here:o204
Source: x0706, commit53bf1b38, FrameAffineSupport.lean.
Literal fine native cube to old observation coordinates and original reference determinant.
-/
import Submission.Lib.K4AffineCubeSupport.Graph
import Submission.Lib.K4OriginalGeometricReference.CoreBasePolynomials

/-!
The literal affine image of a fine native unit cube in an old observation
base. Its determinant is the genuine time/transverse reference ratio.
-/

namespace Submission.Lib.K4AffineCubeSupport

open Set Matrix
open Submission.Lib.K4AffineMeshCaps
open Submission.Lib.K4ChartLifting
open Submission.Lib.K4OriginalGeometricReference.Analytic
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells

noncomputable section

/-- Fine native unit-base coordinates sent into the old observation base. -/
def frameCubeMatrix (old fine : Frame) (κ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  old.obsMatrix * coreBaseMatrix fine κ 1

def frameCubeShift (old fine : Frame) (κ : ℝ) : Fin 3 → ℝ :=
  old.obsMatrix.mulVec (coreBaseShift fine κ 0) + WithLp.ofLp (old.obsBase 0)

/-- No comparison or corrected sheet is used: the affine identity holds
at every original physical base point. -/
theorem frame_cube_coordinates (old fine : Frame)
    (hq : fine.q ≠ 0) (hD : IsUnit fine.D.det) {κ : ℝ} (hκ : κ ≠ 0)
    (v : EuclideanSpace ℝ (Fin 3)) :
    (fun j => old.obsBase v j) =
      affineBase (frameCubeMatrix old fine κ) (frameCubeShift old fine κ)
        (fun j => coreUnitBase κ (fine.obsBase v) j) := by
  let z := coreUnitBase κ (fine.obsBase v)
  have hcore : coreUnitBase κ (fine.obsBase v) =
      WithLp.toLp 2 (fun j => (0 : Fin 3 → ℝ) j + 1 * z j) := by
    ext j
    simp [z]
  have hcoord := coreBaseCoordinates_original fine hq hD hκ 0 1 z v hcore
  have hv : WithLp.ofLp v = (coreBaseMatrix fine κ 1).mulVec (WithLp.ofLp z) +
      coreBaseShift fine κ 0 := by
    funext j
    have hh := hcoord j
    rw [coreBaseCoordinates, affineBaseCoordinates_eval] at hh
    simpa only [Matrix.mulVec, dotProduct, Pi.add_apply, add_comm] using hh.symm
  rw [old.obsBase_eq v]
  change old.obsMatrix.mulVec (WithLp.ofLp v) + WithLp.ofLp (old.obsBase 0) = _
  rw [hv]
  simp only [affineBase, frameCubeMatrix, frameCubeShift,
    Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc, z]

/-- The native time coordinate is unscaled; only the two transverse
unit coordinates contribute the factor four kappa squared. -/
theorem det_coreBaseMatrix (F : Frame) (κ : ℝ) :
    (coreBaseMatrix F κ 1).det = 4 * κ ^ 2 * F.q * F.D.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [coreBaseMatrix]
  ring

theorem det_frameCubeMatrix (old fine : Frame) (κ : ℝ) :
    (frameCubeMatrix old fine κ).det =
      4 * κ ^ 2 * fine.q * fine.D.det / (old.q * old.D.det) := by
  rw [frameCubeMatrix, Matrix.det_mul, old.det_obsMatrix,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', det_coreBaseMatrix]
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem frameCubeMatrix_det_ne_zero (old fine : Frame)
    (hqOld : old.q ≠ 0) (hDOld : IsUnit old.D.det)
    (hqFine : fine.q ≠ 0) (hDFine : IsUnit fine.D.det)
    {κ : ℝ} (hκ : κ ≠ 0) : (frameCubeMatrix old fine κ).det ≠ 0 := by
  rw [det_frameCubeMatrix]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hκ))
    hqFine) hDFine.ne_zero) (mul_ne_zero hqOld hDOld.ne_zero)

/-- Exact original-reference volume, with no old or fine condition
number in the multiplicative constant. -/
theorem abs_det_frameCubeMatrix (old fine : Frame)
    (hqOld : 0 < old.q) (hqFine : 0 < fine.q) (κ : ℝ) :
    |(frameCubeMatrix old fine κ).det| =
      4 * κ ^ 2 * fine.q * |fine.D.det| / (old.q * |old.D.det|) := by
  rw [det_frameCubeMatrix, abs_div]
  simp only [abs_mul, abs_pow, sq_abs, abs_of_pos hqFine, abs_of_pos hqOld]
  norm_num

/-- The original point lies in the actual affine cube whenever its fine
native unit-base point lies in the unit cube. -/
theorem original_mem_frame_affineCube (old fine : Frame)
    (hq : fine.q ≠ 0) (hD : IsUnit fine.D.det) {κ : ℝ} (hκ : κ ≠ 0)
    (v : EuclideanSpace ℝ (Fin 3))
    (hv : (fun j => coreUnitBase κ (fine.obsBase v) j) ∈ Icc 0 1) :
    (fun j => old.obsBase v j) ∈
      affineCube (frameCubeMatrix old fine κ) (frameCubeShift old fine κ) := by
  exact ⟨_, hv, (frame_cube_coordinates old fine hq hD hκ v).symm⟩

/-- A family of actual original fine entries pays its genuine full
reference sum. All shear and eccentricity remain only in hrows. -/
theorem original_frame_joint_family_cover {I X : Type*} [Fintype I]
    (old : Frame) (fine : I → Frame)
    (hqOld : 0 < old.q) (hDOld : IsUnit old.D.det)
    (hqFine : ∀ i, 0 < (fine i).q) (hDFine : ∀ i, IsUnit (fine i).D.det)
    {κ : ℝ} (hκ : κ ≠ 0)
    (V : X → EuclideanSpace ℝ (Fin 3)) (signal : X → ℝ) (A : I → Set X)
    {p s R : ℝ} (hp : 0 < p) (hs : 0 < s) (hR : 0 ≤ R)
    (hrows : ∀ k : I, ∀ i : Fin 3,
      (∑ j : Fin 3, |(frameCubeMatrix old (fine k) κ)⁻¹ i j| * p) ≤ 1)
    (hpoint : ∀ i x, x ∈ A i →
      (fun j => coreUnitBase κ ((fine i).obsBase (V x)) j) ∈ Icc 0 1)
    (hosc : ∀ i x, x ∈ A i → ∀ y, y ∈ A i →
      baseCode p (fun j => old.obsBase (V x) j) =
        baseCode p (fun j => old.obsBase (V y) j) → |signal x - signal y| ≤ R * s) :
    ∃ F : Finset (Fin 4 → ℤ),
      (F.card : ℝ) * p ^ 3 ≤
        108 * κ ^ 2 * (2 * R + 2) / (old.q * |old.D.det|) *
          ∑ i : I, (fine i).q * |(fine i).D.det| ∧
      ∀ i x, x ∈ A i → jointCode p s (fun j => old.obsBase (V x) j) (signal x) ∈ F := by
  have hdet : (∑ i : I, |(frameCubeMatrix old (fine i) κ).det|) =
      (4 * κ ^ 2 / (old.q * |old.D.det|)) *
        ∑ i : I, (fine i).q * |(fine i).D.det| := by
    calc
      _ = ∑ i : I, (4 * κ ^ 2 / (old.q * |old.D.det|)) *
          ((fine i).q * |(fine i).D.det|) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_det_frameCubeMatrix old (fine i) hqOld (hqFine i) κ]
        ring
      _ = _ := (Finset.mul_sum _ _ _).symm
  obtain ⟨F, hF, hcover⟩ := affine_joint_family_cover
    (fun x j => old.obsBase (V x) j) signal A
    (fun i => frameCubeMatrix old (fine i) κ) (fun i => frameCubeShift old (fine i) κ)
    (fun i => frameCubeMatrix_det_ne_zero old (fine i) hqOld.ne' hDOld
      (hqFine i).ne' (hDFine i) hκ) hp hs hR hrows
    (fun i x hx => original_mem_frame_affineCube old (fine i) (hqFine i).ne'
      (hDFine i) hκ (V x) (hpoint i x hx)) hosc
  refine ⟨F, hF.trans_eq ?_, hcover⟩
  rw [hdet]
  ring

end

end Submission.Lib.K4AffineCubeSupport
