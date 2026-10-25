-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.ScalarSupportFromCensus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/ScalarSupportFromCensus.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.ScalarStripCensus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.ScalarSupport

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set MeasureTheory
open Submission.Lib.K4ContinuousKakeya
open WangZahlLot.Obl.wz_slab_local_linearity

noncomputable section

/-- The actual scalar-normal support clause follows from the original
strip-prior floors, original breadth and hereditary physical census.
Neither strip carriers, scalar counts, nor a scalar support certificate
are supplied. Central intercepts may be arbitrarily large. -/
theorem scalar_support_from_original_census (p : PhysicalModel) (ν : Measure Ln)
    [IsFiniteMeasure (p.prior ν)] (hκ : 1 ≤ p.slack)
    (μ : Measure Ev) [IsFiniteMeasure μ] (Kden : NNReal) (hKden : 0 < Kden)
    (Eref E : Set Ev) (hEref : MeasurableSet Eref) (hErefp : Eref ⊆ p.event)
    (hEp : E ⊆ p.event) (hfull : ∀ᵐ z ∂μ, z∈Eref)
    (hdom : μ ≤ Kden • (p.prior ν).prod volume)
    (center : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (W : Finset ℝ)
    {b ρ B η Ksup Kfill dimension ζ Λ Krow : ℝ}
    (hb : 0 < b) (hρ : 0 < ρ) (hbρ : b ≤ ρ)
    (hB : 1 ≤ B) (hη : 0 ≤ η) (hKsup : 0 ≤ Ksup) (hKfill : 0 < Kfill)
    (hdim : 0 ≤ dimension) (hdim1 : dimension ≤ 1)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hΛ : 1 ≤ Λ) (hKrow : 1 ≤ Krow)
    (fineSteps columnSteps : ℝ → ℕ)
    (hwidth : ∀ w∈W, w=b*(2:ℝ)^(fineSteps w))
    (hcolumn : ∀ w∈W, ρ=w*(2:ℝ)^(columnSteps w))
    (hbw : ∀ w∈W, b ≤ w) (hwρ : ∀ w∈W, w ≤ ρ)
    (hsmall : ∀ w∈W, 4*η*ρ+(1+3*B)*b ≤ w/2)
    (hdiam : ∀ z∈E, ∀ i, |p.scalarCoefficients z.1 i-center i| ≤ ρ)
    (hrow : ∀ C j, |row C j| ≤ B) (hF : ∀ z∈E, ‖F z.2‖ ≤ Krow)
    (hrowF : ∀ w∈W, ∀ z∈E, ∀ i : Fin 2,
      |row (p.stripLabel b ρ w row z).1 i.succ-F z.2 i| ≤ η)
    (hscales : ∀ r : ℝ, ζ ≤ r → r ≤ 1 →
      ∃ w∈W, w ≤ ρ*r ∧ ρ*r ≤ Λ*w)
    (Hprior δ failure Cmk : ℝ) (hHprior : 0 ≤ Hprior) (hδ : 0 < δ)
    (hfailure : 0 ≤ failure) (hfailure1 : failure < 1)
    (hCmk : 0 ≤ Cmk) (hMK : FiniteMK 3 Cmk)
    (hfillBudget : (8*Cmk*7^3)^2*(3*(Kden:ℝ)*Hprior)^3 ≤
      ((δ/2)^3/2*(1-failure)^3)*Kfill)
    (hprior : ∀ w∈W, ∀ z∈E, (p.prior ν).real
      (p.stripSupport Eref b ρ w row (p.stripLabel b ρ w row z)) ≤
      (Hprior/ρ)*(μ.restrict ((p.stripLabel b ρ w row) ⁻¹'
        {p.stripLabel b ρ w row z})).real univ)
    (hpositive : ∀ w∈W, ∀ z∈E, μ ((p.stripLabel b ρ w row) ⁻¹'
      {p.stripLabel b ρ w row z}) ≠ 0)
    (hpencil : ∀ q, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ V < 3 →
      μ {z | p.physicalState b z=q ∧
        Metric.infDist (NativeAssigned.direction (p.baseVelocityVector z.1)) (V : Set _) < δ} ≤
        ENNReal.ofReal failure*μ ((p.physicalState b) ⁻¹' {q}))
    (htables : ∀ w∈W, ∀ steps : ℕ, w*(2:ℝ)^steps ≤ 8*ρ →
      ∀ q : ShearedSupport.Code, ∃ P : Finset ShearedSupport.Code,
        (P.card : ℝ) ≤ Ksup*((w*(2:ℝ)^steps)/w)^((3:ℝ)+dimension) ∧
        ∀ z∈Eref, ShearedSupport.code (w*(2:ℝ)^steps) (p.originalPoint z)=q →
          ShearedSupport.code w (p.originalPoint z)∈P) :
    ∀ t, IntervalAD ζ dimension
      ((2*(4*Krow^2+3*Krow)+2)*
        ((27:ℝ)^4*(67584000*B*Ksup*Kfill*(8+6*B))*Λ))
      (p.zoomScalarSet E ρ center F t) := by
  have hw (w : ℝ) (hw : w∈W) : 0 < w := hb.trans_le (hbw w hw)
  apply p.scalar_support_of_original_strip_counts E center F row W
    ρ b B η ζ Λ (67584000*B*Ksup*Kfill*(8+6*B)) dimension Krow
    hρ hb hbρ (zero_le_one.trans hB) hη hζ hζ1 hΛ (by positivity)
    hdim hdim1 hKrow (fun z hz => p.event_time z (hEp hz))
    hdiam hrow hF hw hsmall hrowF hscales
  intro w hwW t ht R a hwR hR1 C N hwitness
  exact p.original_scalar_strip_count_from_census ν hκ μ Kden hKden
    Eref E hEref hErefp hfull hdom center F row hb hρ (hw w hwW)
    hbρ (hbw w hwW) (hwρ w hwW) hB hη hKsup hKfill hdim hdim1
    (fineSteps w) (columnSteps w) (hwidth w hwW) (hcolumn w hwW)
    ht hwR hR1 (hsmall w hwW) (fun l hl => hdiam (l,t) hl) hrow
    (fun l hl => hrowF w hwW (l,t) hl) Hprior δ failure Cmk
    hHprior hδ hfailure hfailure1 hCmk hMK hfillBudget
    (hprior w hwW) (hpositive w hwW) hpencil (htables w hwW) C N hwitness

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
