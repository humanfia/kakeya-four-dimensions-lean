-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.StripFrame, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/StripFrame.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Generalized from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FrozenStripFrame.lean.
The bounded physical model replaces the old chart signal.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenStripFrame.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.StripSupport
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeAssignedCells


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

theorem measurable_position (p : PhysicalModel) : Measurable p.position := by
  have hc := p.measurable_scalarCoefficients
  unfold position
  fun_prop

theorem measurable_velocity (p : PhysicalModel) : Measurable p.velocity := by
  have hc := p.measurable_scalarCoefficients
  unfold velocity
  fun_prop

def baseVelocityVector (p : PhysicalModel) (l : Ln) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (p.velocity l)

theorem measurable_baseVelocityVector (p : PhysicalModel) : Measurable p.baseVelocityVector :=
  (PiLp.volume_preserving_toLp (Fin 3)).measurable.comp p.measurable_velocity

theorem baseVelocityVector_ne_zero (p : PhysicalModel) (l : Ln) : p.baseVelocityVector l ≠ 0 := by
  intro h
  have ht := congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x 0) h
  change p.velocity l 0 = 0 at ht
  rw [p.velocity_time] at ht
  norm_num at ht

/-- The affine anchor of the actual original line, in one coarse
cube's coordinates, is clipped only outside its ORIGINAL support. -/
def stripAnchorVector (p : PhysicalModel) (E : Set Ev) (b ρ width : ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (i : (Fin 4 → ℤ) × ℤ) :
    Ln → EuclideanSpace ℝ (Fin 3) :=
  (p.stripSupport E b ρ width row i).indicator
    (fun l => WithLp.toLp 2 (normalizedStripAnchor (p.position l) (p.velocity l) ρ i.1))

theorem measurable_stripAnchorVector (p : PhysicalModel) {E : Set Ev} (hE : MeasurableSet E)
    (b ρ width : ℝ) (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (i : (Fin 4 → ℤ) × ℤ) :
    Measurable (p.stripAnchorVector E b ρ width row i) := by
  apply Measurable.indicator _ (p.measurableSet_stripSupport hE b ρ width row i)
  have ha := p.measurable_position
  have hv := p.measurable_velocity
  unfold normalizedStripAnchor
  fun_prop

theorem stripAnchorVector_bound (p : PhysicalModel) (hκ : 1 ≤ p.slack)
    {E : Set Ev} (hEp : E ⊆ p.event) {b ρ : ℝ}
    (hb : 0 < b) (hρ : 0 < ρ) (hbρ : b ≤ ρ) (width : ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (i : (Fin 4 → ℤ) × ℤ) (l : Ln) :
    ‖p.stripAnchorVector E b ρ width row i l‖ ≤ 3 * (2 + 34 * p.slack) := by
  by_cases hl : l ∈ p.stripSupport E b ρ width row i
  · rw [stripAnchorVector, Set.indicator_of_mem hl]
    apply NativeAssigned.norm_le_three_of_coord (by linarith)
    intro j
    exact p.stripSupport_anchor_bound hκ hEp hb hρ hbρ width row i l hl j
  · rw [stripAnchorVector, Set.indicator_of_notMem hl, norm_zero]
    linarith

/-- The clipped anchor agrees with the exact normalized original
affine trajectory on every supporting original line. -/
theorem stripAnchorVector_motion (p : PhysicalModel) (E : Set Ev)
    (b width : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (i : (Fin 4 → ℤ) × ℤ)
    (l : Ln) (hl : l ∈ p.stripSupport E b ρ width row i) (t : ℝ) (j : Fin 3) :
    (p.stripAnchorVector E b ρ width row i l +
      ((t - ρ * (i.1 0 : ℝ)) / ρ) • p.baseVelocityVector l) j =
        (originalPhysicalCoordinates (p.signal l) (p.position l) (p.velocity l) t j.castSucc -
          ρ * (i.1 j.castSucc : ℝ)) / ρ := by
  rw [stripAnchorVector, Set.indicator_of_mem hl]
  change normalizedStripAnchor (p.position l) (p.velocity l) ρ i.1 j +
    ((t - ρ * (i.1 0 : ℝ)) / ρ) * p.velocity l j = _
  simpa only [originalPhysicalCoordinates, Fin.snoc_castSucc] using
    normalizedStripAnchor_motion (p.position l) (p.velocity l) hρ i.1 t j

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
