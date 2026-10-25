-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.SourceBridge, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/SourceBridge.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalPreparation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open MeasureTheory Set

noncomputable section

namespace SourceBridge

/-- The original problem arrays read through the source construction API. -/
def problem (p : DensityPreparation.Problem) (S η : ℝ) : ParentSource.Native.ProblemData :=
  ⟨p.N, p.K, p.L, p.d, S, η, p.W, p.ω, p.ν, p.E, p.P, p.B, p.f, p.g, p.G⟩

theorem problem_valid_iff (p : DensityPreparation.Problem) (S η : ℝ) :
    (problem p S η).Valid ↔ p.Valid S η := Iff.rfl

/-- All path assignments and labels are unchanged. -/
def path {W : ℕ} (p : OriginalPath.Data W) : ParentSource.Native.PathData W :=
  ⟨p.r, p.T, p.nw, p.κ, p.C, p.lev, p.par, p.world, p.bin, p.center,
    p.velocity, p.frame, p.test, p.assigned, p.counted, p.lists⟩

theorem path_valid_iff {W : ℕ} (p : OriginalPath.Data W) (Nk L : ℝ)
    (ω : Fin W → ℝ) (ν : Fin W → Measure Ln) (E : Fin W → Set Ev)
    (B : Fin W → ℝ) (f : ℝ → ℝ) (κ₁ : ℝ) (m : ℕ) (s : ℕ → ℝ)
    (δ₀ : ℝ) (Mp Dp : ℕ) (σ : ℝ) :
    (path p).Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ ↔
      p.Valid 0 Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ := Iff.rfl

/-- The frozen analytic hypothesis supplies exactly the jet bound used by
all actual parent-gradient source constructions. -/
theorem denseJetBound_iff (D J : ℕ) :
    ParentSource.Analytic.DenseJetBound D J ↔ JointJetBound D J := Iff.rfl

/-- The source uses the literal unsheared coordinates of the conclusion. -/
theorem unsheared_base {W : ℕ} (p : OriginalPath.Data W) (b : Fin p.C) :
    ParentSource.unshearedPacketBase (path p) b =
      packetBase (p.T (p.lev b)) (p.bin b) (p.center b) (p.velocity b) := by
  rfl

/-- The source signal is the physical global parent divided by the old
thickness, independently of the path's old native test. -/
theorem physical_signal {W : ℕ} (Nk : ℝ) (p : OriginalPath.Data W) (b : Fin p.C)
    (P : Po) :
    ParentSource.physicalParentSignal Nk (path p) b P =
      fun z => packetSignal P z / δ Nk (p.r (p.lev b)) := by
  funext z
  change (δ Nk (p.r (p.lev b)))⁻¹ * packetSignal P z =
    packetSignal P z / δ Nk (p.r (p.lev b))
  rw [div_eq_mul_inv]
  ring

end SourceBridge

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
