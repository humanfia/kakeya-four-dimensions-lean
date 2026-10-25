-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.StripPreparationBudget, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/StripPreparationBudget.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.StripPreparation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.StripCensusGeometry
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.StripBudgetNumerics

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- Convert a final original supporting-prior floor into the literal
real inequality used by determinant strip filling. -/
theorem strip_prior_real_of_floor (ν : Measure Ln) (μ : Measure Ev) [IsFiniteMeasure μ]
    (A : Set Ln) (S : Set Ev) {ρ Hprior : ℝ} (hρ : 0 < ρ) (hHprior : 0 < Hprior)
    (hfloor : ENNReal.ofReal (ρ/Hprior)*ν A ≤ μ S) :
    ν.real A ≤ (Hprior/ρ)*μ.real S := by
  have hh := ENNReal.toReal_mono (measure_ne_top μ S) hfloor
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (div_pos hρ hHprior).le] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (div_pos hHprior hρ).le
  have heq : (Hprior/ρ)*(ρ/Hprior)=1 := by field_simp
  simpa only [←mul_assoc,heq,one_mul,measureReal_def] using hmul

/-- Original strip-prior floors at all tested widths, with explicit
native deletion cost. The partition and the thresholds are constructed
here; one inverse coarse width cancels exactly. -/
theorem exists_original_strip_preparation_with_budget {I : Type*} [Fintype I]
    (p : PhysicalModel) (ν : Measure Ln) (hκ : 1 ≤ p.slack)
    {H : ℝ} (hH : 1 ≤ H)
    (hjets : ∀ l∈p.assigned, |p.scalarCoefficients l 1| ≤ H ∧
      |p.scalarCoefficients l 2| ≤ H ∧ |p.scalarCoefficients l 4| ≤ H ∧
        |p.scalarCoefficients l 6| ≤ H)
    (μ : Measure Ev) [IsFiniteMeasure μ] (field : Ev → Fin 3 → ℝ)
    {E : Set Ev} (hE : MeasurableSet E) (hEp : E ⊆ p.event)
    (hfull : ∀ᵐ z ∂μ, z∈E)
    (ρ b B error L Hprior : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hb : 0 < b) (hbρ : b ≤ ρ) (hB : 0 ≤ B) (he : 0 ≤ error) (hL : 0 ≤ L)
    (hHprior : 0 < Hprior)
    (width : I → ℝ) (hwidth : ∀ i, 0 < width i)
    (hround : ∀ i, (1+3*B)*b ≤ width i)
    (hgraphWidth : ∀ i, error*ρ ≤ width i)
    (hrowWidth : ∀ i, L*H*ρ^2 ≤ width i)
    (hbound : ∀ z∈E, ‖field z‖ ≤ B)
    (hcompare : ∀ z∈E, ∀ z'∈E,
      ‖field z-field z'‖ ≤ L*(‖p.originalPoint z-p.originalPoint z'‖+ρ))
    (hgraph : ∀ z∈E,
      |(p.signal z.1).derivative.eval z.2-∑ j, field z j*p.velocity z.1 j| ≤ error) :
    ∃ row : (Fin 4 → ℤ) → Fin 3 → ℝ, Measurable row ∧
      (∀ C, ‖row C‖ ≤ B) ∧
      (∀ z∈E, ‖field z-row (roundedPhysicalCode b ρ (p.originalPoint z))‖ ≤ 4*L*ρ) ∧
      ∃ U : Set (Fin 4 → ℤ), MeasurableSet U ∧
        μ univ ≤ μ ((p.physicalState b) ⁻¹' U)+
          ENNReal.ofReal ((300*7^8*H)*(Fintype.card I:ℝ)/Hprior)*(p.prior ν) univ ∧
        (∀ i z, p.physicalState b z∈U →
          (p.prior ν).real (p.stripSupport E b ρ (width i) row
            (p.stripLabel b ρ (width i) row z)) ≤
              (Hprior/ρ)*(μ.restrict ((p.physicalState b) ⁻¹' U)).real
                ((p.stripLabel b ρ (width i) row) ⁻¹' {p.stripLabel b ρ (width i) row z})) ∧
        ∀ i z, p.physicalState b z∈U →
          (μ.restrict ((p.physicalState b) ⁻¹' U))
            ((p.stripLabel b ρ (width i) row) ⁻¹' {p.stripLabel b ρ (width i) row z}) ≠ 0 := by
  obtain ⟨D,hD,hscale,hDupper⟩ := exists_strip_partition hH hρ hρ1
  obtain ⟨row,hrow,hrowB,hfit,U,hU,hloss,hfloor,hpositive⟩ :=
    p.exists_original_strip_preparation ν hκ hH hjets μ field hE hEp hfull
      ρ b B error L hρ hb hbρ hB he hL D hD hscale width hwidth
      (fun _ => ENNReal.ofReal (ρ/Hprior)) hbound hcompare hgraph
  have hslot (i : I) :
      ENNReal.ofReal (ρ/Hprior)*
        ENNReal.ofReal (stripVisitBound D ρ b B error (4*L*ρ) H (width i)) ≤
          ENNReal.ofReal ((300*7^8*H)/Hprior) := by
    rw [←ENNReal.ofReal_mul (div_pos hρ hHprior).le]
    apply ENNReal.ofReal_le_ofReal
    apply (mul_le_mul_of_nonneg_left
      (strip_visit_bound_le hρ (hwidth i) (zero_le_one.trans hH) hDupper hB hb.le he hL
        (hround i) (hgraphWidth i) (hrowWidth i)) (div_pos hρ hHprior).le).trans_eq
    field_simp
  have hsum :
      (∑ i : I, ENNReal.ofReal (ρ/Hprior)*
        ENNReal.ofReal (stripVisitBound D ρ b B error (4*L*ρ) H (width i))*(p.prior ν) univ) ≤
      ENNReal.ofReal ((300*7^8*H)*(Fintype.card I:ℝ)/Hprior)*(p.prior ν) univ := by
    calc
      _ ≤ ∑ _i : I, ENNReal.ofReal ((300*7^8*H)/Hprior)*(p.prior ν) univ :=
        Finset.sum_le_sum (fun i _ => mul_le_mul' (hslot i) le_rfl)
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        rw [←mul_assoc,←ENNReal.ofReal_natCast,
          ←ENNReal.ofReal_mul (Nat.cast_nonneg (Fintype.card I))]
        congr 2
        ring
  refine ⟨row,hrow,hrowB,hfit,U,hU,hloss.trans (add_le_add le_rfl hsum),?_,hpositive⟩
  intro i z hz
  exact strip_prior_real_of_floor (p.prior ν) (μ.restrict ((p.physicalState b) ⁻¹' U))
    _ _ hρ hHprior (hfloor i z hz)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
