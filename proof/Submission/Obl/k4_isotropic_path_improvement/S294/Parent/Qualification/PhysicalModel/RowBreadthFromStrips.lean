-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.RowBreadthFromStrips, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph.PhysicalRowLists
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestorBandPencil

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set MeasureTheory
open scoped ENNReal RealInnerProductSpace
open Submission.Lib.K4ThreeBaseRows

noncomputable section

/-- Actual current planar strip ratios imply the unnormalized base
breadth used by physical row regularity, on the exact same state law. -/
theorem row_breadth_of_current_strip_caps (p : PhysicalModel) (μ : Measure Ev)
    [IsFiniteMeasure μ] (E : Set Ev) (hE : MeasurableSet E)
    (hfull : ∀ᵐ z ∂μ, z∈E) {b U width radius failure : ℝ}
    (hU : 0 ≤ U) (hradius : 0 ≤ radius) (hwidth : 2*(U+1)*radius ≤ width)
    (hsmall : radius ≤ 1/4) (hfailure : 0 ≤ failure)
    (hvelocity : ∀ᵐ z ∂μ, ‖p.planarVelocityVector z.1‖ ≤ U)
    (hstrip : ∀ cell (normal : EuclideanSpace ℝ (Fin 2)) offset, ‖normal‖=1 →
      μ {z | p.physicalState b z=cell ∧
        |inner ℝ normal (p.planarVelocityVector z.1)-offset| ≤ width} ≤
          ENNReal.ofReal failure*μ ((p.physicalState b) ⁻¹' {cell})) :
    ∀ cell, Broad (μ.restrict (E∩(p.physicalState b) ⁻¹' {cell}))
      (fun z => SupportedTriples.liftE (Graph.planarVel p z.1)) radius (1-failure) := by
  intro cell V hV
  obtain ⟨normal,offset,hnormal,hnear⟩ := Switch.lift_near_subspace_subset_strip
    V hV U width radius hU hradius hwidth hsmall
  let cellLaw := μ.restrict (E∩(p.physicalState b) ⁻¹' {cell})
  have hcell : MeasurableSet ((p.physicalState b) ⁻¹' {cell}) :=
    (p.measurable_physicalState b) (measurableSet_singleton cell)
  have hcellLaw : cellLaw=μ.restrict ((p.physicalState b) ⁻¹' {cell}) := by
    dsimp only [cellLaw]
    rw [inter_comm,←Measure.restrict_restrict hcell,Measure.restrict_eq_self_of_ae_mem hfull]
  let near := {z : Ev | Metric.infDist
    (SupportedTriples.liftE (Graph.planarVel p z.1)) (V : Set _) < radius}
  let far := {z : Ev | radius ≤ Metric.infDist
    (SupportedTriples.liftE (Graph.planarVel p z.1)) (V : Set _)}
  have hnearMass : cellLaw near ≤ ENNReal.ofReal failure*cellLaw univ := by
    rw [hcellLaw,Measure.restrict_apply' hcell,Measure.restrict_apply_univ]
    apply le_trans (measure_mono_ae ?_) (hstrip cell normal offset hnormal)
    filter_upwards [hvelocity] with z hz
    intro hznear
    refine ⟨hznear.2,hnear (p.planarVelocityVector z.1) hz ?_⟩
    exact hznear.1
  have hcover : (univ : Set Ev) ⊆ far∪near := by
    intro z _
    by_cases hfar : z∈far
    · exact Or.inl hfar
    · apply Or.inr
      change Metric.infDist (SupportedTriples.liftE (Graph.planarVel p z.1)) (V : Set _) < radius
      exact lt_of_not_ge hfar
  have hmass : cellLaw univ ≤ cellLaw far+cellLaw near :=
    (measure_mono hcover).trans (measure_union_le _ _)
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top cellLaw _,measure_ne_top cellLaw _⟩) hmass
  rw [ENNReal.toReal_add (measure_ne_top cellLaw _) (measure_ne_top cellLaw _)] at hreal
  have hnearReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top cellLaw _)) hnearMass
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hfailure] at hnearReal
  change (1-failure)*(cellLaw univ).toReal ≤ (cellLaw far).toReal
  nlinarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
