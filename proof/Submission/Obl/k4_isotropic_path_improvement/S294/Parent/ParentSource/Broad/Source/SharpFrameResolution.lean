-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.SharpFrameResolution, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/SharpFrameResolution.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit adc5136f,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/SharpFrameResolution.lean.
All earlier source attributions below are retained. -/
-- From this LOT tree, o265 session x0943, branch origin/x0943, Broad/Source/SharpFrameResolution.lean.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AffineCoordinates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.FrameExpansion
import Submission.Lib.K4ChartLifting.NormDensityFormula

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set Matrix
open k4_stable_native_signal_oscillation
open Submission.Lib.K4AffineCubeSupport
open Submission.Lib.K4OriginalGeometricReference.Analytic

noncomputable section

private def eventWithPhysicalBase (v : EuclideanSpace ℝ (Fin 3)) : Event :=
  ((0,![v 1,v 2,0,0,0,0]),v 0)

private theorem physicalBase_eventWithPhysicalBase (v : EuclideanSpace ℝ (Fin 3)) :
    (obs 1 1 (eventWithPhysicalBase v)).1=v := by
  ext j
  fin_cases j <;> simp [eventWithPhysicalBase,obs,x]

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → MeasureTheory.Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

/-- Every old base vector is realized by an auxiliary event. This concerns
the global affine coordinate map, independently of source membership. -/
theorem Native.PathData.Valid.surjective_packetBase (old : Fin p.C) :
    Function.Surjective (packetBase p old) := by
  intro v
  let F := nativeOldBaseFrame p old
  refine ⟨eventWithPhysicalBase (F.obsBaseInv v),?_⟩
  unfold packetBase
  rw [physicalBase_eventWithPhysicalBase]
  exact F.obsBase_obsBaseInv (by dsimp [F,nativeOldBaseFrame]; positivity)
    (isUnit_iff_ne_zero.mpr (hp.2.2.2.2.2.2.2 old).2.2.1) v

/-- A common ORIGINAL assigned trajectory bounds every inverse fine/old
cube entry by the actual clock ratio and subpower chart losses. No input
format exponent occurs in the resolution budget. -/
theorem Native.PathData.Valid.packet_cube_inverse_entry_bound
    (hN : 1 ≤ Nk) (old fine : Fin p.C) {l₀ : Ln}
    (hlFine : l₀∈p.A fine) (hlOld : l₀∈p.A old) (r j : Fin 3) :
    |(packetCubeMatrix p old fine)⁻¹ r j| ≤
      (1+4*p.κ+6*p.κ^3*Nk^(2*δ₀*L))*
        ((2:ℝ)^p.T (p.lev fine)/(2:ℝ)^p.T (p.lev old)) := by
  classical
  let M := packetCubeMatrix p old fine
  let Y := fun z : Event => nativeBase (packetNativeCubePoint Nk B p fine z)
  let u : EuclideanSpace ℝ (Fin 3) := PiLp.single 2 j (1:ℝ)
  obtain ⟨z,hz⟩ := hp.surjective_packetBase old u
  obtain ⟨z₀,hz₀⟩ := hp.surjective_packetBase old 0
  have hc (z : Event) : p.nativeBaseCoordinates old z =
      M.mulVec (WithLp.ofLp (Y z))+packetCubeShift p old fine :=
    hp.packet_cube_coordinates old fine z
  have hcoordOld (z : Event) : p.nativeBaseCoordinates old z=WithLp.ofLp (packetBase p old z) :=
    congrArg WithLp.ofLp (p.native_base_coordinates_eq_packetBase old z)
  have hforward : M.mulVec (WithLp.ofLp (Y z-Y z₀))=Pi.single j (1:ℝ) := by
    calc
      _ = (M.mulVec (WithLp.ofLp (Y z))+packetCubeShift p old fine)-
          (M.mulVec (WithLp.ofLp (Y z₀))+packetCubeShift p old fine) := by
        rw [show WithLp.ofLp (Y z-Y z₀)=WithLp.ofLp (Y z)-WithLp.ofLp (Y z₀) by rfl,
          Matrix.mulVec_sub]
        abel
      _ = p.nativeBaseCoordinates old z-p.nativeBaseCoordinates old z₀ := by rw [hc,hc]
      _ = _ := by
        rw [hcoordOld,hcoordOld,hz,hz₀]
        change (Pi.single j (1:ℝ) : Fin 3 → ℝ)-(0 : Fin 3 → ℝ)=Pi.single j (1:ℝ)
        exact sub_zero _
  have hback := congrArg (fun v : Fin 3 → ℝ => M⁻¹.mulVec v) hforward
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul M
    (isUnit_iff_ne_zero.mpr (hp.packet_cube_det_ne_zero old fine)),Matrix.one_mulVec,
    Matrix.mulVec_single_one] at hback
  have hentry : (Y z-Y z₀) r=M⁻¹ r j := congrFun hback r
  have hnorm := hp.local_core_expansion hN old fine (K := 1) (by norm_num) 0 0
    z z₀ hlFine hlOld
  have hnorm' : ‖Y z-Y z₀‖ ≤
      (1+4*p.κ+6*p.κ^3*Nk^(2*δ₀*L))*
        ((2:ℝ)^p.T (p.lev fine)/(2:ℝ)^p.T (p.lev old)) := by
    simpa only [packetLocalCorePoint,pow_zero,one_smul,sub_zero,hz,hz₀,u,
      PiLp.norm_single,norm_one,mul_one,one_mul] using hnorm
  calc
    _ = |(Y z-Y z₀) r| := congrArg abs hentry.symm
    _ ≤ ‖Y z-Y z₀‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (Y z-Y z₀) r
    _ ≤ _ := hnorm'

/-- The complete inverse-row resolution budget follows from the same
original common-line witness. -/
theorem Native.PathData.Valid.packet_cube_inverse_rows_bound
    (hN : 1 ≤ Nk) (old fine : Fin p.C) {l₀ : Ln}
    (hlFine : l₀∈p.A fine) (hlOld : l₀∈p.A old)
    {mesh : ℝ} (hmesh : 0 ≤ mesh) (r : Fin 3) :
    (∑ j : Fin 3, |(packetCubeMatrix p old fine)⁻¹ r j| *mesh) ≤
      3*((1+4*p.κ+6*p.κ^3*Nk^(2*δ₀*L))*
        ((2:ℝ)^p.T (p.lev fine)/(2:ℝ)^p.T (p.lev old)))*mesh := by
  have hh := Finset.sum_le_sum (s := Finset.univ) fun j _ =>
    mul_le_mul_of_nonneg_right (hp.packet_cube_inverse_entry_bound hN old fine hlFine hlOld r j) hmesh
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_ofNat,mul_assoc] using hh

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
