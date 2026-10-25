-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.ScalarStripCensus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/ScalarStripCensus.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.FilledStripCensus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.ScalarIndexRange

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set MeasureTheory
open Submission.Lib.K4ContinuousKakeya

noncomputable section

/-- Choose a dyadic physical coarse mesh covering the normal range of
a tested scalar interval, with a fixed multiplicative enlargement. -/
theorem exists_scalar_census_mesh {ρ width R : ℝ}
    (hw : 0 < width) (hwR : width ≤ ρ*R) :
    ∃ steps : ℕ, 3*ρ*R ≤ width*(2:ℝ)^steps ∧ width*(2:ℝ)^steps ≤ 6*ρ*R := by
  have hρR : 0 < ρ*R := hw.trans_le hwR
  have hone : 1 ≤ (3*ρ*R)/width := (one_le_div hw).mpr (by nlinarith only [hwR,hρR])
  obtain ⟨n,hlo,hhi⟩ := exists_nat_pow_near hone (by norm_num : (1:ℝ) < 2)
  refine ⟨n+1,?_,?_⟩
  · have hh := (div_le_iff₀ hw).mp hhi.le
    simpa only [mul_comm] using hh
  · have hh := (le_div_iff₀ hw).mp hlo
    rw [pow_succ]
    nlinarith only [hh]

/-- The original scalar-strip count is a consequence of MK3 filling,
the original strip-prior floors, and hereditary physical tables. The
normal range and the required intermediate dyadic mesh are chosen here.
No scalar support count or normal-strip carrier is an input. -/
theorem original_scalar_strip_count_from_census (p : PhysicalModel) (ν : Measure Ln)
    [IsFiniteMeasure (p.prior ν)] (hκ : 1 ≤ p.slack)
    (μ : Measure Ev) [IsFiniteMeasure μ] (Kden : NNReal) (hKden : 0 < Kden)
    (Eref E : Set Ev) (hEref : MeasurableSet Eref) (hErefp : Eref ⊆ p.event)
    (hfull : ∀ᵐ z ∂μ, z ∈ Eref) (hdom : μ ≤ Kden • (p.prior ν).prod volume)
    (center : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ)
    {b ρ width B η Ksup Kfill dimension R t a : ℝ}
    (hb : 0 < b) (hρ : 0 < ρ) (hw : 0 < width)
    (hbρ : b ≤ ρ) (hbw : b ≤ width) (hwρ : width ≤ ρ)
    (hB : 1 ≤ B) (hη : 0 ≤ η)
    (hKsup : 0 ≤ Ksup) (hKfill : 0 < Kfill)
    (hdim : 0 ≤ dimension) (hdim1 : dimension ≤ 1)
    (fineSteps columnSteps : ℕ) (hwidth : width=b*(2:ℝ)^fineSteps)
    (hcolumn : ρ=width*(2:ℝ)^columnSteps)
    (ht : t∈Icc (0:ℝ) 1) (hwR : width ≤ ρ*R) (hR1 : R ≤ 1)
    (hsmall : 4*η*ρ+(1+3*B)*b ≤ width/2)
    (hdiam : ∀ l, (l,t)∈E → ∀ i, |p.scalarCoefficients l i-center i| ≤ ρ)
    (hrow : ∀ C j, |row C j| ≤ B)
    (hrowF : ∀ l, (l,t)∈E → ∀ i : Fin 2,
      |row (p.stripLabel b ρ width row (l,t)).1 i.succ-F t i| ≤ η)
    (Hprior δ failure Cmk : ℝ) (hHprior : 0 ≤ Hprior) (hδ : 0 < δ)
    (hfailure : 0 ≤ failure) (hfailure1 : failure < 1)
    (hCmk : 0 ≤ Cmk) (hMK : FiniteMK 3 Cmk)
    (hfillBudget : (8*Cmk*7^3)^2*(3*(Kden:ℝ)*Hprior)^3 ≤
      ((δ/2)^3/2*(1-failure)^3)*Kfill)
    (hprior : ∀ z∈E, (p.prior ν).real
      (p.stripSupport Eref b ρ width row (p.stripLabel b ρ width row z)) ≤
      (Hprior/ρ)*(μ.restrict ((p.stripLabel b ρ width row) ⁻¹'
        {p.stripLabel b ρ width row z})).real univ)
    (hpositive : ∀ z∈E, μ ((p.stripLabel b ρ width row) ⁻¹'
      {p.stripLabel b ρ width row z}) ≠ 0)
    (hpencil : ∀ q, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ V < 3 →
      μ {z | p.physicalState b z=q ∧
        Metric.infDist (NativeAssigned.direction (p.baseVelocityVector z.1)) (V : Set _) < δ} ≤
        ENNReal.ofReal failure*μ ((p.physicalState b) ⁻¹' {q}))
    (htables : ∀ steps : ℕ, width*(2:ℝ)^steps ≤ 8*ρ →
      ∀ q : ShearedSupport.Code, ∃ P : Finset ShearedSupport.Code,
        (P.card : ℝ) ≤ Ksup*((width*(2:ℝ)^steps)/width)^((3:ℝ)+dimension) ∧
        ∀ z∈Eref, ShearedSupport.code (width*(2:ℝ)^steps) (p.originalPoint z)=q →
          ShearedSupport.code width (p.originalPoint z)∈P)
    (C : Fin 4 → ℤ) (N : Finset ℤ)
    (hwitness : ∀ n∈N, ∃ l : Ln, (l,t)∈E ∧ p.stripLabel b ρ width row (l,t)=(C,n) ∧
      Jets2.zS F (Jets2.zoomCoefficients ρ center (p.scalarCoefficients l)) t∈Icc a (a+R)) :
    (N.card : ℝ) ≤ (67584000*B*Ksup*Kfill*(8+6*B))*((ρ*R)/width)^dimension := by
  obtain ⟨steps,hlo,hhi⟩ := exists_scalar_census_mesh hw hwR
  let r := width*(2:ℝ)^steps
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrH : r ≤ 8*ρ := by
    change width*(2:ℝ)^steps ≤ 8*ρ
    have hh : 6*ρ*R ≤ 6*ρ := by nlinarith only [hR1,hρ]
    linarith only [hhi,hh,hρ]
  let offset : Fin 3 → ℤ := fun j => (2:ℤ)^columnSteps*C j.castSucc
  have haligned (j : Fin 3) : ρ*(C j.castSucc : ℝ)=width*(offset j : ℝ) := by
    dsimp only [offset]
    rw [hcolumn,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
    ring
  have hrange := p.original_scalar_strip_index_range E center F row hρ hb hw
    (zero_le_one.trans hB) hη ht hwR hsmall hdiam hrow hrowF C N hwitness
  have hcount := p.original_filled_strip_count ν hκ μ Kden hKden Eref hEref hErefp hfull hdom
    hb hρ hw hr hbρ hbw hwρ (by linarith : ρ ≤ 8*ρ) hrH hB hKsup hKfill
    fineSteps steps hwidth rfl row C (hrow C) offset haligned N
    (fun n hn => (hrange n hn).trans hlo) Hprior δ failure Cmk hHprior hδ hfailure
    hfailure1 hCmk hMK hfillBudget (by
      intro n hn
      obtain ⟨l,hl,hlabel,-⟩ := hwitness n hn
      simpa only [hlabel] using hprior (l,t) hl) (by
      intro n hn
      obtain ⟨l,hl,hlabel,-⟩ := hwitness n hn
      simpa only [hlabel] using hpositive (l,t) hl) hpencil (htables steps hrH)
  have hscale : ((8*ρ)/ρ)^3=(512:ℝ) := by field_simp; norm_num
  rw [hscale] at hcount
  have hρR : 0 < ρ*R := hw.trans_le hwR
  have hpow : (r/width)^dimension ≤ 6*((ρ*R)/width)^dimension := by
    have hratio : r/width ≤ 6*((ρ*R)/width) := by
      apply (div_le_div_of_nonneg_right hhi hw.le).trans_eq
      ring
    calc
      _ ≤ (6*((ρ*R)/width))^dimension :=
        Real.rpow_le_rpow (div_pos hr hw).le hratio hdim
      _ = (6:ℝ)^dimension*((ρ*R)/width)^dimension :=
        Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 6*((ρ*R)/width)^dimension := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 6) hdim1
  apply hcount.trans
  exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans_eq (by ring)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
