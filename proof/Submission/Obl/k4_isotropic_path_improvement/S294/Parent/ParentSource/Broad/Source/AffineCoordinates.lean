-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.AffineCoordinates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/AffineCoordinates.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/AffineCoordinates.lean.
All earlier source attributions below are retained. -/
import Submission.Lib.K4AffineCubeSupport.Frames
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.DeepCoreMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PathBridge
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketNativeLines

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Matrix Analytic
open k4_stable_native_signal_oscillation
open Submission.Lib.K4AffineCubeSupport
open Submission.Lib.K4AffineMeshCaps
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open Submission.Lib.K4OriginalGeometricReference.Analytic (coreUnitBase)

noncomputable section

def matrixEntrySum (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := ∑ i, ∑ j, |M i j|

theorem matrixEntrySum_nonneg (M : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ matrixEntrySum M := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

/-- Resolving the base grid controls the actual inverse affine coordinates. -/
theorem affine_inverse_diameter_of_same_code
    (M : Matrix (Fin 3) (Fin 3) ℝ) (b x y : Fin 3 → ℝ) (hM : M.det ≠ 0)
    {mesh : ℝ} (hm : 0 < mesh)
    (hcode : baseCode mesh (affineBase M b x) = baseCode mesh (affineBase M b y)) :
    ‖WithLp.toLp 2 x - WithLp.toLp 2 y‖ ≤ matrixEntrySum M⁻¹ * mesh := by
  have hcoord (j : Fin 3) : |affineBase M b x j - affineBase M b y j| ≤ mesh := by
    have hh := (Int.abs_sub_lt_one_of_floor_eq_floor (congrFun hcode j)).le
    rw [← sub_div, abs_div, abs_of_pos hm, div_le_one hm] at hh
    exact hh
  have hinv (z : Fin 3 → ℝ) : affineBase M⁻¹ (-(M⁻¹.mulVec b)) (affineBase M b z) = z := by
    simp [affineBase, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      M.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hM), add_assoc]
  have hback (i : Fin 3) : |x i - y i| ≤ ∑ j, |M⁻¹ i j| * mesh := by
    have hh := affineBase_coordinate_variation M⁻¹ (-(M⁻¹.mulVec b)) hcoord i
    rwa [hinv x, hinv y] at hh
  calc
    _ ≤ ∑ i : Fin 3, |(WithLp.toLp 2 x - WithLp.toLp 2 y) i| :=
      Submission.Lib.K4NativePreparationNumerics.euclidean_norm_le_sum_abs _
    _ ≤ ∑ i : Fin 3, ∑ j, |M⁻¹ i j| * mesh :=
      Finset.sum_le_sum (fun i _ => hback i)
    _ = _ := by simp only [matrixEntrySum, Finset.sum_mul]

def packetCubeMatrix {W : ℕ} (p : Native.PathData W) (old fine : Fin p.C) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  frameCubeMatrix (nativeOldBaseFrame p old) (nativeOldBaseFrame p fine) (3 * p.κ)

def packetCubeShift {W : ℕ} (p : Native.PathData W) (old fine : Fin p.C) : Fin 3 → ℝ :=
  frameCubeShift (nativeOldBaseFrame p old) (nativeOldBaseFrame p fine) (3 * p.κ)

theorem packetNativeCube_base_coreUnitBase {W : ℕ} (Nk : ℝ) (B : Fin W → ℝ)
    (p : Native.PathData W) (b : Fin p.C) (q : Event) :
    nativeBase (packetNativeCubePoint Nk B p b q) = coreUnitBase (3 * p.κ) (packetBase p b q) := by
  calc
    _ = WithLp.toLp 2 (fun j : Fin 3 => packetNativeCubePoint Nk B p b q j.castSucc) := by
      ext j
      fin_cases j <;> rfl
    _ = nativeCubeBase (3 * p.κ) (packetBase p b q) := packetNativeCube_base_eq Nk B p b q
    _ = _ := rfl

section Path

variable {W : ℕ} {p : Native.PathData W}
  {Nk L κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
  {ω : Fin W → ℝ} {ν : Fin W → Measure Ln}
  {E : Fin W → Set Ev} {B : Fin W → ℝ} {f : ℝ → ℝ}
  (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

theorem Native.PathData.Valid.packet_cube_det_ne_zero (old fine : Fin p.C) :
    (packetCubeMatrix p old fine).det ≠ 0 := by
  apply frameCubeMatrix_det_ne_zero
  · dsimp [nativeOldBaseFrame]; positivity
  · exact isUnit_iff_ne_zero.mpr (hp.2.2.2.2.2.2.2 old).2.2.1
  · dsimp [nativeOldBaseFrame]; positivity
  · exact isUnit_iff_ne_zero.mpr (hp.2.2.2.2.2.2.2 fine).2.2.1
  · linarith [hp.1]

/-- The native core point and the physical old-base cell are related by
the literal fine/old affine map, at every original incidence. -/
theorem Native.PathData.Valid.packet_cube_coordinates (old fine : Fin p.C) (q : Event) :
    p.nativeBaseCoordinates old q =
      affineBase (packetCubeMatrix p old fine) (packetCubeShift p old fine)
        (fun j => nativeBase (packetNativeCubePoint Nk B p fine q) j) := by
  have hh := frame_cube_coordinates (nativeOldBaseFrame p old) (nativeOldBaseFrame p fine)
    (by dsimp [nativeOldBaseFrame]; positivity)
    (isUnit_iff_ne_zero.mpr (hp.2.2.2.2.2.2.2 fine).2.2.1)
    (show 3 * p.κ ≠ 0 by linarith [hp.1]) (obs 1 1 q).1
  change (fun j => packetBase p old q j) =
    affineBase (packetCubeMatrix p old fine) (packetCubeShift p old fine)
      (fun j => coreUnitBase (3 * p.κ) (packetBase p fine q) j) at hh
  rw [← packetNativeCube_base_coreUnitBase Nk B p fine q] at hh
  have hbase : p.nativeBaseCoordinates old q = fun j => packetBase p old q j := by
    exact congrArg WithLp.ofLp (p.native_base_coordinates_eq_packetBase old q)
  rw [hbase]
  exact hh

theorem Native.PathData.Valid.local_core_diameter_of_same_old_base_cell
    (old fine : Fin p.C) {mesh K : ℝ} (hm : 0 < mesh) (hK : 0 ≤ K)
    (R : ℕ) (center : EuclideanSpace ℝ (Fin 3)) (x y : Event)
    (hcode : baseCode mesh (p.nativeBaseCoordinates old x) =
      baseCode mesh (p.nativeBaseCoordinates old y)) :
    ‖packetLocalCorePoint Nk B p fine K R center x - packetLocalCorePoint Nk B p fine K R center y‖ ≤
      K ^ R * (matrixEntrySum (packetCubeMatrix p old fine)⁻¹ * mesh) := by
  rw [hp.packet_cube_coordinates old fine x, hp.packet_cube_coordinates old fine y] at hcode
  have hh := affine_inverse_diameter_of_same_code (packetCubeMatrix p old fine)
    (packetCubeShift p old fine)
    (fun j => nativeBase (packetNativeCubePoint Nk B p fine x) j)
    (fun j => nativeBase (packetNativeCubePoint Nk B p fine y) j)
    (hp.packet_cube_det_ne_zero old fine) hm hcode
  change ‖(K ^ R) • (_ - center) - (K ^ R) • (_ - center)‖ ≤ _
  rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hK R)]
  exact mul_le_mul_of_nonneg_left hh (pow_nonneg hK R)

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
