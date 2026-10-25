-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ModelIdentities, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ModelIdentities.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ModelIdentities.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.NativePacketModel
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketGeometry
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NormalizedPosteriors

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory

noncomputable section

section Path

variable {W : ℕ} {p : Native.PathData W}
  {Nk L κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
  {ω : Fin W → ℝ} {ν : Fin W → Measure Ln}
  {E : Fin W → Set Ev} {B : Fin W → ℝ} {f : ℝ → ℝ}
  (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

/-- The source caps and the frozen scalar model use the same native frame. -/
theorem Native.PathData.Valid.frozenPacket_frame (b : Fin p.C) :
    (hp.frozenPacket b).unitFrame = nativeOldBaseFrame p b := rfl

theorem Native.PathData.Valid.frozenPacket_line (b : Fin p.C) (l : Ln) :
    (hp.frozenPacket b).line l = normalizedPacketLine p b l := rfl

theorem Native.PathData.Valid.frozenPacket_test (b : Fin p.C) :
    (hp.frozenPacket b).test = normalizedPacketTest Nk p b := rfl

end Path

/-- The velocity used for intrinsic strip breadth is precisely the planar
velocity of the actual normalized original trajectory. -/
theorem native_velocity_eq_normalizedVelocity {W : ℕ} (p : Native.PathData W)
    (b : Fin p.C) (z : Ev) :
    Submission.Lib.K4ChartLifting.velocity (normalizedPacketLine p b z.1) =
      p.normalizedVelocity b z := by
  ext j
  fin_cases j <;>
    simp [normalizedPacketLine, nativeOldBaseFrame,
      Submission.Lib.K4ChartLifting.velocity,
      Submission.Lib.K4ChartLifting.Frame.normTraj,
      Submission.Lib.K4ChartLifting.Frame.normCoeff,
      Native.PathData.normalizedVelocity, Native.v, Submission.Lib.K4ChartLifting.toEuclideanLin_apply_two,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, PiLp.smul_apply] <;> ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
