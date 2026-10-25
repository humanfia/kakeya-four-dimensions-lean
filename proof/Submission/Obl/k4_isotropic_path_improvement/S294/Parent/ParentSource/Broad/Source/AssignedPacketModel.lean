-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.AssignedPacketModel, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/AssignedPacketModel.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/AssignedPacketModel.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPacketScalarModel
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.SelectedPacketLaw

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPacket

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The original indexed lines of the complete old assignment. -/
abbrev AssignedLine (p : FrozenPacket) := ↥p.assigned

def assignedPrior (p : FrozenPacket) (ν : Measure Line) : Measure p.AssignedLine :=
  (p.prior ν).comap ((↑) : p.AssignedLine → Line)

def forgetAssigned (p : FrozenPacket) : p.AssignedLine × ℝ → Incidence :=
  Prod.map ((↑) : p.AssignedLine → Line) id

theorem measurable_forgetAssigned (p : FrozenPacket) : Measurable p.forgetAssigned :=
  measurable_subtype_coe.prodMap measurable_id

theorem prior_assignment (p : FrozenPacket) (ν : Measure Line) :
    ∀ᵐ l ∂p.prior ν, l ∈ p.assigned := by
  rw [p.prior_eq]
  exact Measure.ae_smul_measure (ae_restrict_mem p.measurable_assigned) _

/-- Forgetting the subtype recovers the same full old probability prior. -/
theorem map_assignedPrior (p : FrozenPacket) (ν : Measure Line) :
    (p.assignedPrior ν).map ((↑) : p.AssignedLine → Line) = p.prior ν := by
  rw [assignedPrior, map_comap_subtype_coe p.measurable_assigned]
  exact Measure.restrict_eq_self_of_ae_mem (p.prior_assignment ν)

theorem assignedPrior_probability (p : FrozenPacket) (ν : Measure Line)
    [IsFiniteMeasure ν] (hA : ν p.assigned ≠ 0) :
    IsProbabilityMeasure (p.assignedPrior ν) := by
  letI := p.prior_probability ν hA
  apply (MeasurableEmbedding.subtype_coe p.measurable_assigned).isProbabilityMeasure_comap
  simpa only [Subtype.range_coe] using p.prior_assignment ν

/-- Selecting incidences uses the same full-assignment prior on the subtype. -/
def assignedSelectedEvent (p : FrozenPacket) (J : Set Incidence) :
    Set (p.AssignedLine × ℝ) := p.forgetAssigned ⁻¹' p.selectedEvent J

def assignedSelectedLaw (p : FrozenPacket) (ν : Measure Line) (J : Set Incidence) :
    Measure (p.AssignedLine × ℝ) :=
  ((p.assignedPrior ν).prod volume).restrict (p.assignedSelectedEvent J)

theorem measurable_assignedSelectedEvent (p : FrozenPacket) {J : Set Incidence}
    (hJ : MeasurableSet J) : MeasurableSet (p.assignedSelectedEvent J) :=
  (p.measurable_selectedEvent hJ).preimage p.measurable_forgetAssigned

/-- Both the trajectory index and every selected incidence are recovered
exactly. Restricting the trajectory type has no mass or normalization cost. -/
theorem map_assignedSelectedLaw (p : FrozenPacket) (ν : Measure Line)
    [IsFiniteMeasure ν] (hA : ν p.assigned ≠ 0) {J : Set Incidence}
    (hJ : MeasurableSet J) :
    (p.assignedSelectedLaw ν J).map p.forgetAssigned = p.selectedLaw ν J := by
  letI := p.assignedPrior_probability ν hA
  unfold assignedSelectedLaw assignedSelectedEvent
  rw [← Measure.restrict_map p.measurable_forgetAssigned (p.measurable_selectedEvent hJ)]
  have hprod : ((p.assignedPrior ν).prod volume).map p.forgetAssigned =
      (p.prior ν).prod volume := by
    rw [forgetAssigned, ← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id,
      p.map_assignedPrior, Measure.map_id]
  rw [hprod]
  rfl

theorem assignedSelectedLaw_mass (p : FrozenPacket) (ν : Measure Line)
    [IsFiniteMeasure ν] (hA : ν p.assigned ≠ 0) {J : Set Incidence}
    (hJ : MeasurableSet J) :
    p.assignedSelectedLaw ν J univ = p.selectedLaw ν J univ := by
  rw [← p.map_assignedSelectedLaw ν hA hJ,
    Measure.map_apply p.measurable_forgetAssigned MeasurableSet.univ, preimage_univ]

/-- Every line in this model has the genuine whole-block chart bounds,
independently of any later selected source. -/
theorem assigned_native_bounds (p : FrozenPacket) (l : p.AssignedLine)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖Submission.Lib.K4XInterface.gy (p.line l) t‖ +
        ‖Submission.Lib.K4XInterface.gv (p.line l)‖ ≤ 3 * p.slack ∧
      |p.signalValue l t| ≤ p.slack ∧
      |MvPolynomial.eval (Submission.Lib.K4XInterface.gx (p.line l) t)
          (MvPolynomial.pderiv 3 p.test)| ≤
        p.slack * (p.derivativeScale / Submission.Lib.K4XInterface.gδ p.size p.depth) ∧
      |MvPolynomial.eval (Submission.Lib.K4XInterface.gx (p.line l) t)
          (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 p.test))| ≤
        p.slack * (p.derivativeScale / Submission.Lib.K4XInterface.gδ p.size p.depth) ^ 2 :=
  p.native_bounds l l.property t ht

theorem assigned_scalar_coefficients (p : FrozenPacket) :
    ∀ l : p.AssignedLine, ∀ i, |p.scalarCoefficients l i| ≤ 17 * p.slack :=
  fun l => p.scalar_coefficients_bound l l.property

theorem assignedSelectedEvent_unit_time (p : FrozenPacket) {J : Set Incidence}
    (hJ : J ⊆ p.counted) : p.assignedSelectedEvent J ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
  intro z hz
  exact ⟨mem_univ _, (p.event_unit_time (p.selectedEvent_subset hJ hz)).2⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPacket
