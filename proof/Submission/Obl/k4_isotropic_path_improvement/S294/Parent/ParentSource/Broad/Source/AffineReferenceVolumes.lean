-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.AffineReferenceVolumes, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/AffineReferenceVolumes.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/AffineReferenceVolumes.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ReferenceVolumes
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AffineCoordinates

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open Submission.Lib.K4AffineCubeSupport

noncomputable section

section Path

variable {W : ℕ} {p : Native.PathData W}
  {Nk L κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
  {ω : Fin W → ℝ} {ν : Fin W → Measure Ln}
  {E : Fin W → Set Ev} {B : Fin W → ℝ} {f : ℝ → ℝ}
  (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

/-- The exact affine determinant is charged to genuine original packet
floors. The old reference volume cancels, with no shape or width error. -/
theorem Native.PathData.Valid.affine_reference_volume_sum_le
    (hN : 0 < Nk) (old : Fin p.C) [IsFiniteMeasure (ν (p.γ old))]
    (mid : ℕ) (S : Finset (Fin p.C))
    (hS : ∀ b ∈ S, p.lev b = mid ∧ p.γ b = p.γ old ∧ p.F b ⊆ p.F old) :
    (∑ b ∈ S, |(packetCubeMatrix p old b).det|) ≤
      36 * p.κ ^ 4 * Nk ^ (f (p.r mid) - f (p.r (p.lev old))) := by
  let oldRef := ((2 : ℝ) ^ p.T (p.lev old))⁻¹ * |(p.Q old).det|
  have hold : 0 < oldRef := mul_pos (by positivity)
    (abs_pos.mpr (hp.2.2.2.2.2.2.2 old).2.2.1)
  have hpoint (b : Fin p.C) (hb : b ∈ S) :
      |(packetCubeMatrix p old b).det| = (36 * p.κ ^ 2 / oldRef) *
        (((2 : ℝ) ^ p.T mid)⁻¹ * |(p.Q b).det|) := by
    have hh := abs_det_frameCubeMatrix (nativeOldBaseFrame p old) (nativeOldBaseFrame p b)
      (by dsimp [nativeOldBaseFrame]; positivity) (by dsimp [nativeOldBaseFrame]; positivity)
      (3 * p.κ)
    change |(packetCubeMatrix p old b).det| = _ at hh
    rw [hh]
    dsimp [oldRef, nativeOldBaseFrame]
    rw [(hS b hb).1]
    ring
  have hsum := hp.reference_volume_sum_le hN old mid S hS
  calc
    _ = (36 * p.κ ^ 2 / oldRef) *
        (∑ b ∈ S, ((2 : ℝ) ^ p.T mid)⁻¹ * |(p.Q b).det|) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hpoint
    _ ≤ (36 * p.κ ^ 2 / oldRef) *
        (p.κ ^ 2 * Nk ^ (f (p.r mid) - f (p.r (p.lev old))) * oldRef) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
