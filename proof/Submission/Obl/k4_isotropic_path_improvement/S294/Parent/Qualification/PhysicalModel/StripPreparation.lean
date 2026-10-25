-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.StripPreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/StripPreparation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Generalized from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FrozenStripPreparation.lean.
The bounded physical model replaces the old chart signal.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenStripPreparation.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.StripPruning


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open scoped BigOperators

noncomputable section

/-- From the genuine original field comparison and graph error,
construct the coarse rows and one whole-fine-state restriction with
all final original strip-prior floors. The curve/visit estimates and
finite state carriers are derived from the SAME frozen native packet. -/
theorem exists_original_strip_preparation {I : Type*} [Fintype I]
    (p : PhysicalModel) (ν : Measure Ln) (hκ : 1 ≤ p.slack)
    {H : ℝ} (hH : 1 ≤ H)
    (hjets : ∀ l∈p.assigned, |p.scalarCoefficients l 1| ≤ H ∧
      |p.scalarCoefficients l 2| ≤ H ∧ |p.scalarCoefficients l 4| ≤ H ∧
        |p.scalarCoefficients l 6| ≤ H)
    (μ : Measure Ev) [IsFiniteMeasure μ] (field : Ev → Fin 3 → ℝ)
    {E : Set Ev} (hE : MeasurableSet E) (hEp : E ⊆ p.event)
    (hfull : ∀ᵐ z ∂μ, z ∈ E)
    (ρ b B error L : ℝ) (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b ≤ ρ)
    (hB : 0 ≤ B) (he : 0 ≤ error) (hL : 0 ≤ L)
    (D : ℕ) (hD : 1 ≤ D) (hscale : 3 * H ≤ (D : ℝ) * ρ)
    (width : I → ℝ) (hwidth : ∀ i, 0 < width i) (a : I → ENNReal)
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
      ∃ U : Set (Fin 4 → ℤ), MeasurableSet U ∧
        μ univ ≤ μ ((p.physicalState b) ⁻¹' U) +
          ∑ i : I, a i * ENNReal.ofReal
            (stripVisitBound D ρ b B error (4 * L * ρ) (H) (width i)) *
              (p.prior ν) univ ∧
        (∀ i z, p.physicalState b z ∈ U →
          a i * (p.prior ν) (p.stripSupport E b ρ (width i) row
            (p.stripLabel b ρ (width i) row z)) ≤
          (μ.restrict ((p.physicalState b) ⁻¹' U))
            ((p.stripLabel b ρ (width i) row) ⁻¹' {p.stripLabel b ρ (width i) row z})) ∧
        ∀ i z, p.physicalState b z ∈ U →
          (μ.restrict ((p.physicalState b) ⁻¹' U))
            ((p.stripLabel b ρ (width i) row) ⁻¹' {p.stripLabel b ρ (width i) row z}) ≠ 0 := by
  obtain ⟨row,hm,hBrow,hfit,hbudget⟩ := p.exists_original_strip_budgets ν hH hjets field hE hEp
    ρ b B error L hρ hb hbρ hB he hL D hD hscale hbound hcompare hgraph
  refine ⟨row,hm,hBrow,hfit,?_⟩
  apply p.select_original_strip_family ν hκ μ hEp hfull b ρ hb width row a
    (fun i => ENNReal.ofReal
      (stripVisitBound D ρ b B error (4 * L * ρ) (H) (width i)))
  intro i F
  exact hbudget (width i) (hwidth i) F

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
