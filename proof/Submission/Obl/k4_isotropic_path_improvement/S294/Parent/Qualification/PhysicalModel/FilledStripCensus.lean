-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.FilledStripCensus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/FilledStripCensus.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.StripCensusGeometry

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set MeasureTheory
open Submission.Lib.K4ContinuousKakeya

noncomputable section

theorem filling_card_lower {ρ width c D Kfill : ℝ}
    (hρ : 0 < ρ) (hw : 0 < width) (hc : 0 < c) (hKfill : 0 < Kfill)
    (n : ℕ) (hfill : c ≤ (n : ℝ)*D*(width/ρ)^3) (hbudget : D ≤ c*Kfill) :
    (ρ/width)^3/Kfill ≤ (n : ℝ) := by
  have hmain : c ≤ (n : ℝ)*(c*Kfill)*(width/ρ)^3 :=
    hfill.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg n)) (by positivity))
  have heq : c = ((ρ/width)^3/Kfill)*(c*Kfill*(width/ρ)^3) := by
    simp only [div_pow]
    field_simp
    <;> ring
  have hmain' : ((ρ/width)^3/Kfill)*(c*Kfill*(width/ρ)^3) ≤
      (n : ℝ)*(c*Kfill*(width/ρ)^3) := by
    rw [←heq]
    simpa only [mul_assoc] using hmain
  exact (mul_le_mul_iff_left₀ (by positivity : 0 < c*Kfill*(width/ρ)^3)).mp hmain'

/-- Actual original strip filling supplies every witness carrier used
in the scalar census. Only genuine original reference bounds, strip
breadth and hereditary physical tables remain as hypotheses. -/
theorem original_filled_strip_count (p : PhysicalModel) (ν : Measure Ln)
    [IsFiniteMeasure (p.prior ν)] (hκ : 1 ≤ p.slack)
    (μ : Measure Ev) [IsFiniteMeasure μ] (Kden : NNReal) (hKden : 0 < Kden)
    (E : Set Ev) (hE : MeasurableSet E) (hEp : E ⊆ p.event)
    (hfull : ∀ᵐ z ∂μ, z ∈ E) (hdom : μ ≤ Kden • (p.prior ν).prod volume)
    {b ρ width r H B Ksup Kfill dimension center : ℝ}
    (hb : 0 < b) (hρ : 0 < ρ) (hw : 0 < width) (hr : 0 < r)
    (hbρ : b ≤ ρ) (hbw : b ≤ width) (hwρ : width ≤ ρ)
    (hρH : ρ ≤ H) (hrH : r ≤ H) (hB : 1 ≤ B) (hKsup : 0 ≤ Ksup) (hKfill : 0 < Kfill)
    (fineSteps coarseSteps : ℕ) (hwidth : width=b*(2:ℝ)^fineSteps)
    (hrwidth : r=width*(2:ℝ)^coarseSteps)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (C : Fin 4 → ℤ)
    (hrow : ∀ j, |row C j| ≤ B) (offset : Fin 3 → ℤ)
    (haligned : ∀ j : Fin 3, ρ*(C j.castSucc : ℝ)=width*(offset j : ℝ))
    (N : Finset ℤ) (hrange : ∀ n ∈ N, |width*(n : ℝ)-center|+width ≤ r)
    (Hprior δ failure Cmk : ℝ) (hHprior : 0 ≤ Hprior) (hδ : 0 < δ)
    (hfailure : 0 ≤ failure) (hfailure1 : failure < 1)
    (hCmk : 0 ≤ Cmk) (hMK : FiniteMK 3 Cmk)
    (hfillBudget : (8*Cmk*7^3)^2*(3*(Kden:ℝ)*Hprior)^3 ≤
      ((δ/2)^3/2*(1-failure)^3)*Kfill)
    (hprior : ∀ n ∈ N, (p.prior ν).real (p.stripSupport E b ρ width row (C,n)) ≤
      (Hprior/ρ)*(μ.restrict ((p.stripLabel b ρ width row) ⁻¹' {(C,n)})).real univ)
    (hpositive : ∀ n ∈ N, μ ((p.stripLabel b ρ width row) ⁻¹' {(C,n)}) ≠ 0)
    (hpencil : ∀ q, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ V < 3 →
      μ {z | p.physicalState b z=q ∧
        Metric.infDist (NativeAssigned.direction (p.baseVelocityVector z.1)) (V : Set _) < δ} ≤
        ENNReal.ofReal failure*μ ((p.physicalState b) ⁻¹' {q}))
    (htables : ∀ q : ShearedSupport.Code, ∃ F : Finset ShearedSupport.Code,
      (F.card : ℝ) ≤ Ksup*(r/width)^((3:ℝ)+dimension) ∧
      ∀ z ∈ E, ShearedSupport.code r (p.originalPoint z)=q →
        ShearedSupport.code width (p.originalPoint z)∈F) :
    (N.card : ℝ) ≤ 22000*B*Ksup*Kfill*(8+6*B)*(H/ρ)^3*(r/width)^dimension := by
  classical
  let U : Set Ev := {z | z∈E ∧ ∃ n∈N, p.stripLabel b ρ width row z=(C,n)}
  let corner : Fin 3 → ℝ := fun j => ρ*(C j.castSucc : ℝ)
  let base : Ev → Fin 3 → ℤ := fun z => NativeAssigned.code ρ b (width/ρ) corner
    (p.physicalState b z)
  let baseMap : ShearedSupport.Code → Fin 3 → ℤ := fun q j => q.1 j-offset j
  have hround (z : Ev) : ShearedSupport.code width (p.roundedPoint b z)=
      ShearedSupport.code width (p.originalPoint z) := by
    rw [hwidth]
    exact p.rounded_code_dyadic hb fineSteps z
  have hroundR (z : Ev) : ShearedSupport.code r (p.roundedPoint b z)=
      ShearedSupport.code r (p.originalPoint z) := by
    rw [hrwidth,ShearedSupport.code_dyadic_coarsens (p.roundedPoint b),
      ShearedSupport.code_dyadic_coarsens p.originalPoint,hround]
  apply NormalStripCensus.count_from_actual_filling U (p.roundedPoint b) (row C) corner
    (ParentSource.coarsenProductGrid coarseSteps coarseSteps) base baseMap N
    hρ hr hw hrH hB hKsup hKfill hrow
  · intro z hz
    rw [hrwidth]
    exact ShearedSupport.code_dyadic_coarsens (p.roundedPoint b) width coarseSteps z
  · intro z hz
    exact p.assigned_code_of_physical_code b hρ hw corner offset haligned z
  · intro z hz j
    obtain ⟨hz,n,hn,hlabel⟩ := hz
    exact (p.stripLabel_base_box b width hρ row hlabel j).trans hρH
  · intro z hz
    obtain ⟨hz,n,hn,hlabel⟩ := hz
    exact p.stripLabel_normal_slab b ρ hw row hlabel (hrange n hn)
  · intro q
    obtain ⟨F,hF,hcover⟩ := htables q
    refine ⟨F,hF,?_⟩
    intro z hz hq
    rw [hround]
    exact hcover z hz.1 ((hroundR z).symm.trans hq)
  · intro n hn
    have hmass : 0 < (μ.restrict ((p.stripLabel b ρ width row) ⁻¹' {(C,n)})).real univ := by
      change 0 < ((μ.restrict ((p.stripLabel b ρ width row) ⁻¹' {(C,n)})) univ).toReal
      rw [Measure.restrict_apply_univ]
      exact ENNReal.toReal_pos (hpositive n hn) (measure_ne_top _ _)
    obtain ⟨W,hWcover,hWpositive,hWfill⟩ := p.original_strip_base_filling ν hκ μ Kden hKden
      hE hEp hfull hdom b ρ width hb hρ hw hbρ hbw hwρ row (C,n)
      Hprior δ failure Cmk hHprior hδ hfailure hfailure1.le hCmk hMK
      (hprior n hn) hmass hpencil
    refine ⟨W,?_,?_⟩
    · exact filling_card_lower hρ hw (by have := sub_pos.mpr hfailure1; positivity)
        hKfill W.card (by simpa only [mul_assoc] using hWfill) hfillBudget
    · intro w hwW
      obtain ⟨z,hz,hlabel,hbase⟩ := p.strip_filling_witness μ hfull b ρ width row (C,n) w
        (hWpositive w hwW)
      exact ⟨z,⟨hz,n,hn,hlabel⟩,(p.stripLabel_coordinates b ρ width row hlabel).2,hbase⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
