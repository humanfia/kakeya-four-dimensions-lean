-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.TimeRow, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/TimeRow.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Generalized from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FrozenTimeRow.lean.
The bounded physical model replaces the old chart signal.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenTimeRow.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.PacketStrips
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.StripSupport


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

theorem physical_norm_le_scalar_position_norm (p : PhysicalModel) (z z' : Ev) :
    ‖originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2 -
      originalPhysicalCoordinates (p.signal z'.1) (p.position z'.1) (p.velocity z'.1) z'.2‖ ≤
        ‖Jets2.zpos (p.scalarCoefficients z.1) z.2 -
          Jets2.zpos (p.scalarCoefficients z'.1) z'.2‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  change |originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2 j -
    originalPhysicalCoordinates (p.signal z'.1) (p.position z'.1) (p.velocity z'.1) z'.2 j| ≤ _
  rw [p.physical_scalar_coord,p.physical_scalar_coord]
  exact norm_le_pi_norm
    (Jets2.zpos (p.scalarCoefficients z.1) z.2 - Jets2.zpos (p.scalarCoefficients z'.1) z'.2)
    (physicalIndex j)

/-- Construct the actual time-only row in an original parameter
world. The native coefficient bounds, original physical comparison
and constructed coarse-row fit imply every scalar-normal row estimate. -/
theorem exists_original_zoom_time_row (p : PhysicalModel)
    (E : Set Ev) (hEp : E ⊆ p.event) (field : Ev → Fin 3 → ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (b ρ K B L : ℝ)
    (hρ : 0 < ρ) (hK : 1 ≤ K) (hL : 0 ≤ L)
    (hjets : ∀ z∈E, |p.scalarCoefficients z.1 1| ≤ K ∧
      |p.scalarCoefficients z.1 2| ≤ K ∧ |p.scalarCoefficients z.1 4| ≤ K ∧
        |p.scalarCoefficients z.1 6| ≤ K)
    (hbound : ∀ z ∈ E, ‖field z‖ ≤ B)
    (hdiam : ∀ z ∈ E, ∀ z' ∈ E, ∀ i,
      |p.scalarCoefficients z.1 i - p.scalarCoefficients z'.1 i| ≤ ρ)
    (hcompare : ∀ z ∈ E, ∀ z' ∈ E,
      ‖field z - field z'‖ ≤ L *
        (‖originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2 -
          originalPhysicalCoordinates (p.signal z'.1) (p.position z'.1) (p.velocity z'.1) z'.2‖ + ρ))
    (hcoarse : ∀ z ∈ E,
      ‖field z - row (roundedPhysicalCode b ρ
        (originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2))‖ ≤
          4 * L * ρ) :
    ∃ F : ℝ → Fin 2 → ℝ, Measurable F ∧
      (∀ z ∈ E, ‖F z.2‖ ≤ B) ∧
      (∀ z ∈ E, ‖F z.2 - (fun i : Fin 2 => field z i.succ)‖ ≤ 2 * ((3 * K + 1) * L) * ρ) ∧
      (∀ width : ℝ, ∀ z ∈ E, ∀ i : Fin 2,
        |row (p.stripLabel b ρ width row z).1 i.succ - F z.2 i| ≤ 6 * (K + 1) * L * ρ) ∧
      ∀ z ∈ E, ∀ z' ∈ E,
        ‖F z.2 - F z'.2‖ ≤ 3 * ((3 * K + 1) * L) * (|z.2 - z'.2| + ρ) := by
  let tangential : Ev → Fin 2 → ℝ := fun z i => field z i.succ
  have hdrop (z z' : Ev) : ‖tangential z - tangential z'‖ ≤ ‖field z - field z'‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    exact norm_le_pi_norm (field z - field z') i.succ
  have htBound : ∀ z ∈ E, ‖tangential z‖ ≤ B := by
    intro z hz
    apply (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hbound z hz))).mpr
    intro i
    exact (norm_le_pi_norm (field z) i.succ).trans (hbound z hz)
  have htCompare : ∀ z ∈ E, ∀ z' ∈ E,
      ‖tangential z - tangential z'‖ ≤ L *
        (‖Jets2.zpos (p.scalarCoefficients z.1) z.2 -
          Jets2.zpos (p.scalarCoefficients z'.1) z'.2‖ + ρ) := by
    intro z hz z' hz'
    exact (hdrop z z').trans ((hcompare z hz z' hz').trans
      (mul_le_mul_of_nonneg_left (add_le_add (p.physical_norm_le_scalar_position_norm z z') le_rfl) hL))
  obtain ⟨F,hm,hFb,hfit,hcmp⟩ := Jets2.exists_zoom_time_row_of_jets E p.scalarCoefficients tangential
    ρ K B L hρ hK hL (fun z hz => (p.event_unit_time (hEp hz)).2)
    hjets hdiam htBound htCompare
  refine ⟨F,hm,hFb,hfit,?_,hcmp⟩
  intro width z hz i
  have hg : |field z i.succ - row (p.stripLabel b ρ width row z).1 i.succ| ≤ 4 * L * ρ := by
    rw [p.stripLabel_coarse]
    exact (norm_le_pi_norm _ i.succ).trans (hcoarse z hz)
  have hf : |F z.2 i - field z i.succ| ≤ 2 * ((3 * K + 1) * L) * ρ :=
    (norm_le_pi_norm _ i).trans (hfit z hz)
  calc
    _ ≤ |row (p.stripLabel b ρ width row z).1 i.succ - field z i.succ| +
        |field z i.succ - F z.2 i| := abs_sub_le _ _ _
    _ ≤ 4 * L * ρ + 2 * ((3 * K + 1) * L) * ρ :=
      add_le_add (by simpa only [abs_sub_comm] using hg) (by simpa only [abs_sub_comm] using hf)
    _ = _ := by ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
