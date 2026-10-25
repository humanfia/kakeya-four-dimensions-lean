-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.UnshearedFrameResolution, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/UnshearedFrameResolution.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/UnshearedFrameResolution.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.UnshearedAffineCoordinates

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open MeasureTheory Set Native Matrix
open k4_stable_native_signal_oscillation
open Submission.Lib.K4AffineMeshCaps
open Submission.Lib.K4AffineCubeSupport
noncomputable section

private def unshearedEventWithPhysicalBase (v : EuclideanSpace ℝ (Fin 3)) : Ev :=
  ((0,![v 1,v 2,0,0,0,0]),v 0)

private theorem originalPhysicalBase_unshearedEvent (v : EuclideanSpace ℝ (Fin 3)) :
    originalPhysicalBase (unshearedEventWithPhysicalBase v)=v := by
  ext i
  fin_cases i <;> simp [originalPhysicalBase,unshearedEventWithPhysicalBase,xp]

theorem surjective_unshearedPacketBase {W : ℕ} (p : PathData W) (old : Fin p.C) :
    Function.Surjective (unshearedPacketBase p old) := by
  let F := unshearedOldBaseFrame p old
  have hq : F.q ≠ 0 := by dsimp [F,unshearedOldBaseFrame]; positivity
  have hD : IsUnit F.D.det := by
    apply isUnit_iff_ne_zero.mpr
    change (unshearedOldBaseFrame p old).D.det ≠ 0
    rw [unshearedOldBaseFrame_det]
    positivity
  intro v
  refine ⟨unshearedEventWithPhysicalBase (F.obsBaseInv v),?_⟩
  have hb := congrFun (unshearedOldBaseFrame_obsBase p old)
    (unshearedEventWithPhysicalBase (F.obsBaseInv v))
  change F.obsBase (originalPhysicalBase (unshearedEventWithPhysicalBase (F.obsBaseInv v)))=_ at hb
  rw [originalPhysicalBase_unshearedEvent,F.obsBase_obsBaseInv hq hD] at hb
  exact hb.symm

section Path
variable {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
include hp

/-- The inverse of every actual fine-to-unsheared-old cube is bounded
by original path and clock quantities, without input-format exponents. -/
theorem Native.PathData.Valid.unsheared_packet_cube_inverse_entry_bound
    (hN : 1 ≤ N) (old fine : Fin p.C) {l₀ : Ln}
    (hlFine : l₀∈p.A fine) (hlOld : l₀∈p.A old) (r j : Fin 3) :
    |(unshearedPacketCubeMatrix p old fine)⁻¹ r j| ≤
      ((1+4*p.κ+6*p.κ^3*N^(2*δ₀*L))*
        ((2:ℝ)^p.T (p.lev fine)/(2:ℝ)^p.T (p.lev old)))*
          (1+2*(p.κ*N^(2*δ₀*L))*(1+‖p.u old‖)) := by
  classical
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hNp : 0 < N := zero_lt_one.trans_le hN
  let M := unshearedPacketCubeMatrix p old fine
  let Y := fun z : Ev => nativeBase (packetNativeCubePoint N B p fine z)
  let u : EuclideanSpace ℝ (Fin 3) := PiLp.single 2 j (1:ℝ)
  obtain ⟨z,hz⟩ := surjective_unshearedPacketBase p old u
  obtain ⟨z₀,hz₀⟩ := surjective_unshearedPacketBase p old 0
  have hc (z : Ev) : WithLp.ofLp (unshearedPacketBase p old z)=
      M.mulVec (WithLp.ofLp (Y z))+unshearedPacketCubeShift p old fine :=
    hp.unsheared_packet_cube_coordinates old fine z
  have hforward : M.mulVec (WithLp.ofLp (Y z-Y z₀))=Pi.single j (1:ℝ) := by
    calc
      _ = (M.mulVec (WithLp.ofLp (Y z))+unshearedPacketCubeShift p old fine)-
          (M.mulVec (WithLp.ofLp (Y z₀))+unshearedPacketCubeShift p old fine) := by
        rw [show WithLp.ofLp (Y z-Y z₀)=WithLp.ofLp (Y z)-WithLp.ofLp (Y z₀) by rfl,
          Matrix.mulVec_sub]
        abel
      _ = WithLp.ofLp (unshearedPacketBase p old z)-
          WithLp.ofLp (unshearedPacketBase p old z₀) := by rw [hc,hc]
      _ = _ := by
        rw [hz,hz₀]
        exact sub_zero _
  have hback := congrArg (fun v : Fin 3 → ℝ => M⁻¹.mulVec v) hforward
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul M
    (isUnit_iff_ne_zero.mpr (hp.unsheared_packet_cube_det_ne_zero old fine)),
    Matrix.one_mulVec,Matrix.mulVec_single_one] at hback
  have hentry : (Y z-Y z₀) r=M⁻¹ r j := congrFun hback r
  have hcomp := hp.native_base_le_unsheared hN old z z₀
  rw [hz,hz₀,sub_zero] at hcomp
  simp only [u,PiLp.norm_single,norm_one,mul_one] at hcomp
  have hexpand := hp.local_core_expansion hN old fine (K:=1) (by norm_num) 0 0 z z₀ hlFine hlOld
  have hexpand' : ‖Y z-Y z₀‖ ≤
      ((1+4*p.κ+6*p.κ^3*N^(2*δ₀*L))*
        ((2:ℝ)^p.T (p.lev fine)/(2:ℝ)^p.T (p.lev old)))*
        ‖packetBase p old z-packetBase p old z₀‖ := by
    simpa only [packetLocalCorePoint,pow_zero,one_smul,sub_zero,one_mul] using hexpand
  calc
    _ = |(Y z-Y z₀) r| := congrArg abs hentry.symm
    _ ≤ ‖Y z-Y z₀‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (Y z-Y z₀) r
    _ ≤ _ := hexpand'.trans (mul_le_mul_of_nonneg_left hcomp (by positivity))

/-- Actual inverse row budgets at every requested base mesh. -/
theorem Native.PathData.Valid.unsheared_packet_cube_inverse_rows_bound
    (hN : 1 ≤ N) (old fine : Fin p.C) {l₀ : Ln}
    (hlFine : l₀∈p.A fine) (hlOld : l₀∈p.A old)
    {base : ℝ} (hbase : 0 ≤ base) (r : Fin 3) :
    (∑ j : Fin 3, |(unshearedPacketCubeMatrix p old fine)⁻¹ r j| *base) ≤
      3*(((1+4*p.κ+6*p.κ^3*N^(2*δ₀*L))*
        ((2:ℝ)^p.T (p.lev fine)/(2:ℝ)^p.T (p.lev old)))*
          (1+2*(p.κ*N^(2*δ₀*L))*(1+‖p.u old‖)))*base := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) fun j _ =>
    mul_le_mul_of_nonneg_right
      (hp.unsheared_packet_cube_inverse_entry_bound hN old fine hlFine hlOld r j) hbase
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_ofNat,mul_assoc] using hh

end Path
end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
