-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Direct.BoundedPacketModel, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/Direct/BoundedPacketModel.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.AncestorSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalPrior

/-! A globally bounded coefficient table for a genuine original packet.
The full original assignment prior and the actual selected event are fixed.
Only trajectories outside the displayed coefficient bound are changed. -/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Direct

open Set MeasureTheory
open Qualification

noncomputable section

/-- This cutoff is independent of successful incidences and witness times. -/
def boundedTable (c : Ln → Fin 7 → ℝ) (C : ℝ) (l : Ln) : Fin 7 → ℝ := by
  classical
  exact if l ∈ PhysicalModel.coefficientSet c C then c l else 0

theorem measurable_boundedTable (c : Ln → Fin 7 → ℝ) (hc : Measurable c) (C : ℝ) :
    Measurable (boundedTable c C) :=
  Measurable.ite (PhysicalModel.measurableSet_coefficientSet c hc C) hc measurable_const

theorem boundedTable_eq (c : Ln → Fin 7 → ℝ) (C : ℝ) {l : Ln}
    (hl : ∀ i, |c l i| ≤ C) : boundedTable c C l=c l :=
  if_pos hl

theorem boundedTable_bound (c : Ln → Fin 7 → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (l : Ln) (i : Fin 7) : |boundedTable c C l i| ≤ C := by
  unfold boundedTable
  split_ifs with hl
  · exact hl i
  · simpa only [Pi.zero_apply,abs_zero] using hC

section Packet

variable (f : AncestorSource.Packet) (c : Ln → Fin 7 → ℝ) (hc : Measurable c)
    (C : ℝ) (hC : 0 ≤ C) (U : Set Ev) (hU : MeasurableSet U)
    (hUF : U⊆f.counted) (hcoeff : ∀ z∈U, ∀ i, |c z.1 i| ≤ C)

/-- A genuine unit-clock model with literal original assignment and prior.
Its coefficient bound holds on ALL indexed trajectories. -/
def boundedPacketModel : PhysicalModel where
  scalarCoefficients := boundedTable c C
  measurable_scalarCoefficients := measurable_boundedTable c hc C
  assigned := f.assigned
  measurable_assigned := f.measurable_assigned
  slack := C
  scalar_coefficients_bound := fun l _ i =>
    (boundedTable_bound c hC l i).trans (by linarith)
  event := f.selectedEvent U
  measurable_event := f.measurable_selectedEvent hU
  event_assignment := fun z hz => f.event_assignment (f.selectedEvent_subset hUF hz)
  event_time := fun z hz => (f.event_unit_time (f.selectedEvent_subset hUF hz)).2

include hcoeff in
/-- On an actual source line the entire table is unchanged, at ALL times. -/
theorem boundedPacketModel_coefficients {z : Ev}
    (hz : z∈(boundedPacketModel f c hc C hC U hU hUF).event) :
    (boundedPacketModel f c hc C hC U hU hUF).scalarCoefficients z.1=c z.1 := by
  obtain ⟨q,hq,rfl⟩ := hz
  change boundedTable c C (f.timeChange q).1=c (f.timeChange q).1
  rw [f.timeChange_apply]
  exact boundedTable_eq c C (hcoeff q hq)

/-- Every native qualification jet has the small amplitude bound globally. -/
theorem boundedPacketModel_jets (l : Ln) (i : Fin 7) :
    |(boundedPacketModel f c hc C hC U hU hUF).scalarCoefficients l i| ≤ C :=
  boundedTable_bound c hC l i

/-- This equality is literal; there is no selected-event denominator. -/
theorem boundedPacketModel_prior (ν : Measure Ln) :
    (boundedPacketModel f c hc C hC U hU hUF).prior ν=f.prior ν :=
  (f.prior_eq ν).symm

/-- The actual original coefficient law is unchanged when the displayed
bound holds on the full assignment almost everywhere. -/
theorem boundedPacketModel_coefficients_ae (ν : Measure Ln)
    (hae : ∀ᵐ l ∂ν, l∈f.assigned → ∀ i, |c l i| ≤ C) :
    ∀ᵐ l ∂(f.prior ν),
      (boundedPacketModel f c hc C hC U hU hUF).scalarCoefficients l=c l := by
  have heq : ∀ᵐ l ∂ν.restrict f.assigned, boundedTable c C l=c l := by
    filter_upwards [ae_restrict_mem f.measurable_assigned,
      ae_mono Measure.restrict_le_self hae] with l hl hbound
    exact boundedTable_eq c C (hbound hl)
  rw [f.prior_eq]
  exact Measure.ae_smul_measure heq ((ν f.assigned)⁻¹)

/-- Density is computed from the SAME full original assignment reference. -/
theorem boundedPacketModel_density (ν : Measure Ln) [IsFiniteMeasure ν]
    (hA : ν f.assigned≠0) {mass : ENNReal}
    (hmass : mass*(ENNReal.ofReal f.unitFrame.q*ν f.assigned)≤(ν.prod volume) U) :
    IsProbabilityMeasure ((boundedPacketModel f c hc C hC U hU hUF).prior ν) ∧
      mass≤(((boundedPacketModel f c hc C hC U hU hUF).prior ν).prod volume)
        (boundedPacketModel f c hc C hC U hU hUF).event := by
  have h := AncestorSource.selected_density f ν hA U hU hUF hmass
  rw [boundedPacketModel_prior]
  exact ⟨h.1,h.2.2.2⟩

end Packet
end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Direct
