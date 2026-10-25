-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.OriginalPrior, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/OriginalPrior.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.Interface

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open MeasureTheory Set

noncomputable section

/-- A measurable coefficient cutoff used only to impose an almost-everywhere
original bound pointwise. -/
def coefficientSet (c : Ln → Fin 7 → ℝ) (B : ℝ) : Set Ln :=
  {l | ∀ i, |c l i| ≤ B}

theorem measurableSet_coefficientSet (c : Ln → Fin 7 → ℝ) (hc : Measurable c) (B : ℝ) :
    MeasurableSet (coefficientSet c B) := by
  simpa only [coefficientSet, ofPred_forall, Function.comp_apply] using
    MeasurableSet.iInter (fun i : Fin 7 => measurableSet_le
      (((measurable_pi_apply i).comp hc).abs) measurable_const)

/-- A physical quadratic model on the original trajectories. Its only new
assignment restriction is the displayed coefficient bound. -/
def ofCoefficients (c : Ln → Fin 7 → ℝ) (hc : Measurable c)
    (A : Set Ln) (hA : MeasurableSet A) (B : ℝ) (hB : 0 ≤ B)
    (E : Set Ev) (hE : MeasurableSet E)
    (hEA : ∀ z ∈ E, z.1 ∈ A) (htime : ∀ z ∈ E, z.2 ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ z ∈ E, ∀ i, |c z.1 i| ≤ B) : PhysicalModel where
  scalarCoefficients := c
  measurable_scalarCoefficients := hc
  assigned := A ∩ coefficientSet c B
  measurable_assigned := hA.inter (measurableSet_coefficientSet c hc B)
  slack := B
  scalar_coefficients_bound := fun l hl i => (hl.2 i).trans (by linarith)
  event := E
  measurable_event := hE
  event_assignment := fun z hz => ⟨hEA z hz, hcoeff z hz⟩
  event_time := htime

/-- An almost-everywhere coefficient cutoff leaves the FULL original
assignment prior exactly unchanged. -/
theorem ofCoefficients_prior (c : Ln → Fin 7 → ℝ) (hc : Measurable c)
    (A : Set Ln) (hA : MeasurableSet A) (B : ℝ) (hB : 0 ≤ B)
    (E : Set Ev) (hE : MeasurableSet E)
    (hEA : ∀ z ∈ E, z.1 ∈ A) (htime : ∀ z ∈ E, z.2 ∈ Icc (0 : ℝ) 1)
    (hcoeff : ∀ z ∈ E, ∀ i, |c z.1 i| ≤ B)
    (ν : Measure Ln) (hae : ∀ᵐ l ∂ν, l ∈ A → ∀ i, |c l i| ≤ B) :
    (ofCoefficients c hc A hA B hB E hE hEA htime hcoeff).prior ν =
      (ν A)⁻¹ • ν.restrict A := by
  have hset : A ∩ coefficientSet c B =ᵐ[ν] A := by
    filter_upwards [hae] with l hl
    simp only [mem_inter_iff, mem_ofPred_eq, coefficientSet]
    exact propext (and_iff_left_of_imp hl)
  have hrestrict := Measure.restrict_congr_set hset
  have hmass : ν (A ∩ coefficientSet c B) = ν A := measure_congr hset
  change (ν (A ∩ coefficientSet c B))⁻¹ • ν.restrict (A ∩ coefficientSet c B) = _
  rw [hmass, hrestrict]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
