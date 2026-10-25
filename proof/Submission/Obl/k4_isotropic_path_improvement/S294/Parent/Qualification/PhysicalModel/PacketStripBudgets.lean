-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.PacketStripBudgets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/PacketStripBudgets.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Generalized from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FrozenPacketStripBudgets.lean.
The bounded physical model replaces the old chart signal.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenPacketStripBudgets.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.PacketStrips
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CoarsePhysicalRows


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

/-- Construct ONE actual coarse row per physical cube, then control
the supporting ORIGINAL trajectory priors at EVERY normal-strip width.
The row is chosen before the widths and finite strip families. -/
theorem exists_original_strip_budgets (p : PhysicalModel) (ν : Measure Ln)
    {H : ℝ} (hH : 1 ≤ H)
    (hjets : ∀ l∈p.assigned, |p.scalarCoefficients l 1| ≤ H ∧
      |p.scalarCoefficients l 2| ≤ H ∧ |p.scalarCoefficients l 4| ≤ H ∧
        |p.scalarCoefficients l 6| ≤ H) (field : Ev → Fin 3 → ℝ)
    {E : Set Ev} (hE : MeasurableSet E) (hEp : E ⊆ p.event)
    (ρ b B error L : ℝ) (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b ≤ ρ)
    (hB : 0 ≤ B) (he : 0 ≤ error) (hL : 0 ≤ L)
    (D : ℕ) (hD : 1 ≤ D) (hscale : 3 * H ≤ (D : ℝ) * ρ)
    (hbound : ∀ z ∈ E, ‖field z‖ ≤ B)
    (hcompare : ∀ z ∈ E, ∀ z' ∈ E,
      ‖field z - field z'‖ ≤ L *
        (‖originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2 -
          originalPhysicalCoordinates (p.signal z'.1) (p.position z'.1) (p.velocity z'.1) z'.2‖ + ρ))
    (hgraph : ∀ z ∈ E,
      |(p.signal z.1).derivative.eval z.2 - ∑ j, field z j * p.velocity z.1 j| ≤ error) :
    ∃ row : (Fin 4 → ℤ) → Fin 3 → ℝ, Measurable row ∧
      (∀ C, ‖row C‖ ≤ B) ∧
      (∀ z ∈ E, ‖field z - row (roundedPhysicalCode b ρ
        (originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2))‖ ≤
          4 * L * ρ) ∧
      ∀ width : ℝ, 0 < width → ∀ F : Finset ((Fin 4 → ℤ) × ℤ),
        (∑ i ∈ F, (p.prior ν) (originalOccupationSupport volume
          (originalStripDensity E (originalStripLabel b ρ width row p.signal p.position p.velocity) i))) ≤
            ENNReal.ofReal (stripVisitBound D ρ b B error (4 * L * ρ) (H) width) *
              (p.prior ν) univ := by
  obtain ⟨row, hrow, hrowB, hfit⟩ := exists_original_coarse_rows E
    (fun z => originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2)
    field b ρ B L hb hρ hbρ hB hL hbound hcompare
  refine ⟨row, hrow, hrowB, hfit, ?_⟩
  intro width hw F
  apply p.strip_support_prior_budget ν hH hjets row field hE hEp F ρ b B error (4 * L * ρ) width
    hρ hb hbρ hB he (by positivity) hw D hD hscale
  · intro C j
    exact (norm_le_pi_norm (row C) j).trans (hrowB C)
  · exact hgraph
  · intro z hz j
    exact (norm_le_pi_norm
      (field z - row (roundedPhysicalCode b ρ
        (originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2))) j).trans
      (hfit z hz)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
