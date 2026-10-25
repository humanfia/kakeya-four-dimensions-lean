-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalNativeCoordinates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/OriginalNativeCoordinates.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/OriginalNativeCoordinates.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AssignedOriginalCuts
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ModelIdentities
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PhysicalCodePruning

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open SourceGeometry

noncomputable section

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

theorem Native.PathData.Valid.originalIncidence_time (old : Fin p.C)
    (z : (hp.frozenPacket old).AssignedLine × ℝ) :
    packetTime p old ((hp.frozenPacket old).originalIncidence z) = z.2 := by
  let packet := hp.frozenPacket old
  have hh := congrArg Prod.snd (packet.timeChange_apply (packet.originalIncidence z))
  rw [show packet.timeChange (packet.originalIncidence z) = packet.forgetAssigned z from
    packet.timeChange.apply_symm_apply _] at hh
  have hframe : packet.unitFrame = nativeOldBaseFrame p old := rfl
  rw [hframe] at hh
  change z.2 = (nativeOldBaseFrame p old).q⁻¹ *
    ((packet.originalIncidence z).2 - (nativeOldBaseFrame p old).t₀) at hh
  simpa only [packetTime, div_eq_mul_inv, mul_comm] using hh.symm

/-- The original support count and the native Kakeya curve see exactly
the same physical point, on the same original assigned line. -/
theorem Native.PathData.Valid.assigned_physical_point (old : Fin p.C)
    (z : (hp.frozenPacket old).AssignedLine × ℝ) :
    packetPhysicalPoint Nk p old ((hp.frozenPacket old).originalIncidence z) =
      nativePhysicalCurve (normalizedPacketTest Nk p old)
        (normalizedPacketPosition p old z.1) (normalizedPacketVelocity p old z.1) z.2 := by
  rw [packetPhysicalPoint_eq_nativeCurve hp, hp.originalIncidence_time,
    (hp.frozenPacket old).originalIncidence_fst]

theorem Native.PathData.Valid.assigned_physical_code (old : Fin p.C)
    (baseMesh hidden : ℝ) (z : (hp.frozenPacket old).AssignedLine × ℝ) :
    p.originalPhysicalCode Nk old baseMesh hidden ((hp.frozenPacket old).originalIncidence z) =
      fun j => ⌊nativePhysicalCurve (normalizedPacketTest Nk p old)
        (normalizedPacketPosition p old z.1) (normalizedPacketVelocity p old z.1) z.2 j /
          (if j = 3 then hidden else baseMesh)⌋ := by
  rw [p.originalPhysicalCode_coordinates, hp.assigned_physical_point]

theorem Native.PathData.Valid.measurable_assigned_physical_curve (old : Fin p.C) :
    Measurable (fun z : (hp.frozenPacket old).AssignedLine × ℝ =>
      nativePhysicalCurve (normalizedPacketTest Nk p old)
        (normalizedPacketPosition p old z.1) (normalizedPacketVelocity p old z.1) z.2) := by
  have hh := (measurable_packetPhysicalPoint Nk p old).comp
    (hp.frozenPacket old).measurable_originalIncidence
  convert hh using 1
  funext z
  exact (hp.assigned_physical_point old z).symm

theorem Native.PathData.Valid.assigned_whole_native_curve (old : Fin p.C)
    (l : (hp.frozenPacket old).AssignedLine) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |MvPolynomial.eval (fun j => normalizedPacketPosition p old l j +
        t * normalizedPacketVelocity p old l j) (normalizedPacketTest Nk p old)| ≤ p.κ := by
  rw [← normalizedPacketMotion]
  exact (normalizedPacket_native_bounds hp old l l.property t ht).2.1

theorem Native.PathData.Valid.assigned_base_velocity_bound (old : Fin p.C)
    (l : (hp.frozenPacket old).AssignedLine) (j : Fin 3) :
    |normalizedPacketVelocity p old l j.castSucc| ≤ 3 * p.κ := by
  have hn := (normalizedPacket_native_bounds hp old l l.property 0 (by norm_num)).1
  have hv : ‖Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.v
      (normalizedPacketLine p old l)‖ ≤ 3 * p.κ :=
    (le_add_of_nonneg_left (norm_nonneg
      (Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.y (normalizedPacketLine p old l) 0))).trans hn
  fin_cases j
  · change |(1 : ℝ)| ≤ 3 * p.κ
    rw [abs_one]
    linarith [hp.1]
  · exact (PiLp.norm_apply_le _ 0).trans hv
  · exact (PiLp.norm_apply_le _ 1).trans hv

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
