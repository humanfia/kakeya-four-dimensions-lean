-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.UnshearedAffineCoordinates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/UnshearedAffineCoordinates.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/UnshearedAffineCoordinates.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.UnshearedBaseComparison
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AffineReferenceVolumes
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.SharpJointResolution
import Submission.Lib.K4ChartLifting.NormDensityFormula

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open MeasureTheory Set Native Matrix
open k4_stable_native_signal_oscillation
open Submission.Lib.K4AffineMeshCaps
open Submission.Lib.K4AffineCubeSupport
open Submission.Lib.K4OriginalGeometricReference.Analytic
noncomputable section

def unshearedPacketCubeMatrix {W : ℕ} (p : PathData W) (old fine : Fin p.C) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  frameCubeMatrix (unshearedOldBaseFrame p old) (nativeOldBaseFrame p fine) (3*p.κ)

def unshearedPacketCubeShift {W : ℕ} (p : PathData W) (old fine : Fin p.C) : Fin 3 → ℝ :=
  frameCubeShift (unshearedOldBaseFrame p old) (nativeOldBaseFrame p fine) (3*p.κ)

section Path
variable {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
include hp

theorem Native.PathData.Valid.unsheared_packet_cube_det_ne_zero (old fine : Fin p.C) :
    (unshearedPacketCubeMatrix p old fine).det ≠ 0 := by
  apply frameCubeMatrix_det_ne_zero
  · dsimp [unshearedOldBaseFrame]; positivity
  · apply isUnit_iff_ne_zero.mpr
    rw [unshearedOldBaseFrame_det]
    positivity
  · dsimp [nativeOldBaseFrame]; positivity
  · exact isUnit_iff_ne_zero.mpr (hp.2.2.2.2.2.2.2 fine).2.2.1
  · linarith [hp.1]

/-- Literal fine native cube to unsheared old physical coordinates. -/
theorem Native.PathData.Valid.unsheared_packet_cube_coordinates
    (old fine : Fin p.C) (z : Ev) :
    (fun j => unshearedPacketBase p old z j) =
      affineBase (unshearedPacketCubeMatrix p old fine) (unshearedPacketCubeShift p old fine)
        (fun j => nativeBase (packetNativeCubePoint N B p fine z) j) := by
  have hh := frame_cube_coordinates (unshearedOldBaseFrame p old) (nativeOldBaseFrame p fine)
    (by dsimp [nativeOldBaseFrame]; positivity)
    (isUnit_iff_ne_zero.mpr (hp.2.2.2.2.2.2.2 fine).2.2.1)
    (show 3*p.κ ≠ 0 by linarith [hp.1]) (originalPhysicalBase z)
  have hb := congrFun (unshearedOldBaseFrame_obsBase p old) z
  change (unshearedOldBaseFrame p old).obsBase (originalPhysicalBase z)=_ at hb
  rw [hb] at hh
  change (fun j => unshearedPacketBase p old z j)=
    affineBase (unshearedPacketCubeMatrix p old fine) (unshearedPacketCubeShift p old fine)
      (fun j => coreUnitBase (3*p.κ) (packetBase p fine z) j) at hh
  rw [←packetNativeCube_base_coreUnitBase N B p fine z] at hh
  exact hh

/-- The change of old base multiplies every fine affine volume by the
same genuine old spatial determinant ratio. -/
theorem Native.PathData.Valid.unsheared_packet_cube_det_ratio (old fine : Fin p.C) :
    |(unshearedPacketCubeMatrix p old fine).det| =
      (|(p.Q old).det|/(((2:ℝ)^p.T (p.lev old))⁻¹)^2)*
        |(packetCubeMatrix p old fine).det| := by
  have hD : (p.Q old).det ≠ 0 := (hp.2.2.2.2.2.2.2 old).2.2.1
  have hu := abs_det_frameCubeMatrix (unshearedOldBaseFrame p old) (nativeOldBaseFrame p fine)
    (by dsimp [unshearedOldBaseFrame]; positivity)
    (by dsimp [nativeOldBaseFrame]; positivity) (3*p.κ)
  have hn := abs_det_frameCubeMatrix (nativeOldBaseFrame p old) (nativeOldBaseFrame p fine)
    (by dsimp [nativeOldBaseFrame]; positivity)
    (by dsimp [nativeOldBaseFrame]; positivity) (3*p.κ)
  change |(unshearedPacketCubeMatrix p old fine).det|=_ at hu
  change |(packetCubeMatrix p old fine).det|=_ at hn
  rw [hu,hn,unshearedOldBaseFrame_det]
  dsimp [unshearedOldBaseFrame,nativeOldBaseFrame]
  rw [abs_of_nonneg (sq_nonneg (((2:ℝ)^p.T (p.lev old))⁻¹))]
  field_simp [hD]
  <;> ring

/-- The old isotropic determinant ratio costs only the existing path tolerance. -/
theorem Native.PathData.Valid.unsheared_determinant_ratio_le
    (hN : 1 ≤ N) (old : Fin p.C) :
    |(p.Q old).det|/(((2:ℝ)^p.T (p.lev old))⁻¹)^2 ≤ N^(2*δ₀*L) := by
  rcases hp.2.2.2.2.2.2.2 old with
    ⟨hlev, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdetup, _⟩
  obtain ⟨_, _, _, _, hnw, _⟩ := hp.2.2.2.2.1 (p.lev old) hlev
  simp only [zero_mul,sub_zero] at hnw
  have hnwge : -δ₀*L ≤ p.nw (p.lev old) := by
    have hh := (abs_le.mp hnw).1
    linarith
  have hraw : |(p.Q old).det| *(4:ℝ)^p.T (p.lev old) ≤ N^(2*δ₀*L) :=
    hdetup.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
  have hpow : (4:ℝ)^p.T (p.lev old)=((2:ℝ)^p.T (p.lev old))^2 := by
    rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,←pow_mul,←pow_mul,Nat.mul_comm]
  rw [hpow] at hraw
  simpa only [div_eq_mul_inv,inv_pow,inv_inv] using hraw

/-- Summing literal unsheared affine volumes preserves the original
fine/old profile saving, with one old tolerance factor. -/
theorem Native.PathData.Valid.unsheared_affine_reference_volume_sum_le
    (hN : 1 ≤ N) (old : Fin p.C) [IsFiniteMeasure (ν (p.γ old))]
    (mid : ℕ) (S : Finset (Fin p.C))
    (hS : ∀ b∈S, p.lev b=mid ∧ p.γ b=p.γ old ∧ p.F b⊆p.F old) :
    (∑ b∈S, |(unshearedPacketCubeMatrix p old b).det|) ≤
      N^(2*δ₀*L)*(36*p.κ^4*N^(f (p.r mid)-f (p.r (p.lev old)))) := by
  have hsum := hp.affine_reference_volume_sum_le (zero_lt_one.trans_le hN) old mid S hS
  calc
    _ = (|(p.Q old).det|/(((2:ℝ)^p.T (p.lev old))⁻¹)^2)*
        (∑ b∈S, |(packetCubeMatrix p old b).det|) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun b _ => hp.unsheared_packet_cube_det_ratio old b)
    _ ≤ _ := mul_le_mul (hp.unsheared_determinant_ratio_le hN old) hsum
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)

end Path
end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
