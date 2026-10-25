-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.AncestorFrames, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/AncestorFrames.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SourceBridge
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.CenterVelocity

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open MeasureTheory Set

noncomputable section

namespace AncestorFrames

open ParentSource ParentSource.Native

/-- Translation disappears from a difference of literal unsheared bases.
Multiplying by its own clock gives the original physical difference. -/
theorem scaled_base_difference {W : ℕ} (p : PathData W) (b : Fin p.C) (z z' : Ev) :
    (((2 : ℝ) ^ p.T (p.lev b))⁻¹) •
      (unshearedPacketBase p b z - unshearedPacketBase p b z') =
        originalPhysicalBase z - originalPhysicalBase z' := by
  ext j
  fin_cases j <;>
    simp [unshearedPacketBase, originalPhysicalBase] <;> field_simp <;> ring

/-- The clock factors cancel exactly between any two unsheared frames,
without an ancestry or assignment hypothesis. -/
theorem scaled_base_distance {W : ℕ} (p : PathData W) (b b' : Fin p.C) (z z' : Ev) :
    (((2 : ℝ) ^ p.T (p.lev b))⁻¹) *
      ‖unshearedPacketBase p b z - unshearedPacketBase p b z'‖ =
        (((2 : ℝ) ^ p.T (p.lev b'))⁻¹) *
          ‖unshearedPacketBase p b' z - unshearedPacketBase p b' z'‖ := by
  have hh (a : Fin p.C) :
      (((2 : ℝ) ^ p.T (p.lev a))⁻¹) *
        ‖unshearedPacketBase p a z - unshearedPacketBase p a z'‖ =
          ‖originalPhysicalBase z - originalPhysicalBase z'‖ := by
    rw [← scaled_base_difference p a z z', norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < ((2 : ℝ) ^ p.T (p.lev a))⁻¹)]
  exact (hh b).trans (hh b').symm

/-- Transfer one raw-core pair estimate from its active broad packet to
any ancestor frame, with the native-to-unsheared comparison displayed. -/
theorem pair_estimate_in_frame {W : ℕ} {p : PathData W} {N L : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Ln} {E : Fin W → Set Ev}
    {B : Fin W → ℝ} {f : ℝ → ℝ} {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hN : 1 ≤ N)
    (b target : Fin p.C) (signal : Ev → ℝ) (z z' : Ev)
    {error slope comparison : ℝ} (hslope : 0 ≤ slope)
    (hcomparison : 1 + 2 * (p.κ * N ^ (2 * δ₀ * L)) * (1 + ‖p.u b‖) ≤ comparison)
    (hpair : |signal z - signal z'| ≤ error + slope *
      (((2 : ℝ) ^ p.T (p.lev b))⁻¹) * ‖ParentSource.packetBase p b z - ParentSource.packetBase p b z'‖) :
    |signal z - signal z'| ≤ error + slope * comparison *
      (((2 : ℝ) ^ p.T (p.lev target))⁻¹) *
        ‖unshearedPacketBase p target z - unshearedPacketBase p target z'‖ := by
  have hc := hp.native_base_le_unsheared hN b z z'
  have hclock : 0 ≤ ((2 : ℝ) ^ p.T (p.lev b))⁻¹ := by positivity
  calc
    _ ≤ error + slope * (((2 : ℝ) ^ p.T (p.lev b))⁻¹) *
        ((1 + 2 * (p.κ * N ^ (2 * δ₀ * L)) * (1 + ‖p.u b‖)) *
          ‖unshearedPacketBase p b z - unshearedPacketBase p b z'‖) :=
      hpair.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (mul_nonneg hslope hclock)))
    _ ≤ error + slope * (((2 : ℝ) ^ p.T (p.lev b))⁻¹) *
        (comparison * ‖unshearedPacketBase p b z - unshearedPacketBase p b z'‖) := by
      gcongr
    _ = error + slope * comparison *
        ((((2 : ℝ) ^ p.T (p.lev b))⁻¹) *
          ‖unshearedPacketBase p b z - unshearedPacketBase p b z'‖) := by ring
    _ = _ := by rw [scaled_base_distance p b target]; ring

end AncestorFrames

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
