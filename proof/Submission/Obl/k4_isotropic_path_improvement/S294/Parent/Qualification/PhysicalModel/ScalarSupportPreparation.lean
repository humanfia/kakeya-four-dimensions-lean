-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.ScalarSupportPreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/ScalarSupportPreparation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.HereditaryTables
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.StripPreparationBudget
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.ScalarSupportFromCensus

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set MeasureTheory
open Submission.Lib.K4ParentSignalPreparation.Census
open Submission.Lib.K4ContinuousKakeya
open WangZahlLot.Obl.wz_slab_local_linearity
open scoped ENNReal BigOperators

noncomputable section

/-- Whole original physical states preserve the original pencil bound. -/
theorem pencil_bound_under_whole_state_cut (p : PhysicalModel) (μ : Measure Ev)
    (b δ failure : ℝ) (U : Set (Fin 4 → ℤ))
    (hpencil : ∀ q, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ V < 3 →
      μ {z | p.physicalState b z=q ∧
        Metric.infDist (NativeAssigned.direction (p.baseVelocityVector z.1)) (V : Set _) < δ} ≤
        ENNReal.ofReal failure*μ ((p.physicalState b) ⁻¹' {q})) :
    ∀ q, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)), Module.finrank ℝ V < 3 →
      (μ.restrict ((p.physicalState b) ⁻¹' U))
        {z | p.physicalState b z=q ∧
          Metric.infDist (NativeAssigned.direction (p.baseVelocityVector z.1)) (V : Set _) < δ} ≤
        ENNReal.ofReal failure*(μ.restrict ((p.physicalState b) ⁻¹' U))
          ((p.physicalState b) ⁻¹' {q}) := by
  intro q V hV
  have hh := ParentSource.state_ratio_under_whole_cell_cut μ (p.physicalState b)
    (p.measurable_physicalState b) ((p.physicalState b) ⁻¹' U) (by
      intro x y hxy
      change p.physicalState b x∈U ↔ p.physicalState b y∈U
      rw [hxy])
    {z | Metric.infDist (NativeAssigned.direction (p.baseVelocityVector z.1)) (V : Set _) < δ}
    (ENNReal.ofReal failure) (fun q => hpencil q V hV) q
  exact hh

/-- Construct scalar support on one fixed original source, before any
coefficient-world selection. Both the hereditary tables and the strip
prior floors are derived internally, on common whole-finest-state cuts.
Any later world and its actual time-row approximation inherit the result. -/
theorem exists_original_scalar_support_preparation_resolved (p : PhysicalModel) (ν : Measure Ln)
    [IsProbabilityMeasure (p.prior ν)] (hκ : 1 ≤ p.slack)
    {H : ℝ} (hH : 1 ≤ H)
    (hjets : ∀ l∈p.assigned, |p.scalarCoefficients l 1| ≤ H ∧
      |p.scalarCoefficients l 2| ≤ H ∧ |p.scalarCoefficients l 4| ≤ H ∧
        |p.scalarCoefficients l 6| ≤ H)
    (μ : Measure Ev) [IsFiniteMeasure μ] (Kden : NNReal) (hKden : 0 < Kden)
    (E : Set Ev) (hE : MeasurableSet E) (hEp : E ⊆ p.event)
    (hfull : ∀ᵐ z ∂μ, z∈E) (hdom : μ ≤ Kden • (p.prior ν).prod volume)
    (field : Ev → Fin 3 → ℝ) (W : Finset ℝ)
    {ε θ Kcensus dimension Cband rate b ρ B error L Hprior : ℝ}
    (hε : 0 < ε) (hθ : 0 < θ) (hKcensus : 1 ≤ Kcensus) (hθK : θ ≤ Kcensus)
    (hCband : 0 ≤ Cband) (hrate : 0 < rate)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρθ : ρ ≤ θ)
    (steps : ℕ) (hsteps : Kcensus^(100:ℕ) ≤ (2:ℝ)^steps)
    (hb_eq : b=ε*(2:ℝ)^steps) (hbρ : b ≤ ρ)
    (hB : 1 ≤ B) (he : 0 ≤ error) (hL : 0 ≤ L) (hHprior : 0 < Hprior)
    (fineSteps columnSteps : ℝ → ℕ)
    (hwidth : ∀ w∈W, w=b*(2:ℝ)^(fineSteps w))
    (hcolumn : ∀ w∈W, ρ=w*(2:ℝ)^(columnSteps w))
    (hbw : ∀ w∈W, b ≤ w) (hwρ : ∀ w∈W, w ≤ ρ)
    (hround : ∀ w∈W, (1+3*B)*b ≤ w)
    (hgraphWidth : ∀ w∈W, error*ρ ≤ w)
    (hrowWidth : ∀ w∈W, L*H*ρ^2 ≤ w)
    (hbound : ∀ z∈E, ‖field z‖ ≤ B)
    (hcompare : ∀ z∈E, ∀ z'∈E,
      ‖field z-field z'‖ ≤ L*(‖p.originalPoint z-p.originalPoint z'‖+ρ))
    (hgraph : ∀ z∈E,
      |(p.signal z.1).derivative.eval z.2-∑ j, field z j*p.velocity z.1 j| ≤ error)
    (hcensus : ∀ a w : ℝ, ε ≤ a → a ≤ 1 → ε ≤ w → w ≤ 1 →
      Kcensus^(100:ℕ)*a ≤ θ*w →
        (occupied E (fun x j => p.originalBase x j) (fun x => p.originalPoint x 3/θ) a w).Finite ∧
        ((occupied E (fun x j => p.originalBase x j)
          (fun x => p.originalPoint x 3/θ) a w).ncard:ℝ) ≤ Kcensus/(a^3*w^dimension))
    (reference : ENNReal) (href : 0 < reference) (hreftop : reference ≠ ⊤)
    (hband : ∀ R : ℝ, ε ≤ R → R ≤ 8*ρ →
      ∀ U : Set P3, MeasurableSet U → ∀ c : P3 → ℝ, Measurable c →
      μ {x | p.originalBase x∈U ∧ |p.originalPoint x 3-c (p.originalBase x)| ≤ R} ≤
        ENNReal.ofReal (Cband*θ^(-dimension)*R^dimension)*reference*volume U)
    (δ failure Cmk Kfill : ℝ) (hδ : 0 < δ) (hfailure : 0 ≤ failure)
    (hfailure1 : failure < 1) (hCmk : 0 ≤ Cmk) (hMK : FiniteMK 3 Cmk)
    (hKfill : 0 < Kfill) (hdim : 0 ≤ dimension) (hdim1 : dimension ≤ 1)
    (hfillBudget : (8*Cmk*7^3)^2*(3*(Kden:ℝ)*Hprior)^3 ≤
      ((δ/2)^3/2*(1-failure)^3)*Kfill)
    (hpencil : ∀ q, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ V < 3 →
      μ {z | p.physicalState b z=q ∧
        Metric.infDist (NativeAssigned.direction (p.baseVelocityVector z.1)) (V : Set _) < δ} ≤
        ENNReal.ofReal failure*μ ((p.physicalState b) ⁻¹' {q})) :
    ∃ (U0 U1 : Set (Fin 4 → ℤ)) (row : (Fin 4 → ℤ) → Fin 3 → ℝ),
      MeasurableSet U0 ∧ MeasurableSet U1 ∧ Measurable row ∧ (∀ C, ‖row C‖ ≤ B) ∧
      let R0 := (p.physicalState b) ⁻¹' U0
      let R1 := (p.physicalState b) ⁻¹' U1
      let current := (μ.restrict R0).restrict R1
      μ univ ≤ current univ+
        ENNReal.ofReal ((300*7^8*H)*(W.card:ℝ)/Hprior)+
        ENNReal.ofReal ((Kcensus*((2:ℝ)^steps)^3)*((W.card:ℝ)*rate))*reference ∧
      ∀ (A : Set Ev), A ⊆ E ∩ R0 ∩ R1 →
      ∀ (center : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ) (ηF ζ Λ Krow : ℝ),
        0 ≤ ηF → 0 < ζ → ζ ≤ 1 → 1 ≤ Λ → 1 ≤ Krow →
        (∀ z∈A, ∀ i, |p.scalarCoefficients z.1 i-center i| ≤ ρ) →
        (∀ z∈A, ‖F z.2‖ ≤ Krow) →
        (∀ z∈A, ∀ i : Fin 2, |field z i.succ-F z.2 i| ≤ ηF) →
        (∀ w∈W, 4*(ηF+4*L*ρ)*ρ+(1+3*B)*b ≤ w/2) →
        (∀ r : ℝ, ζ ≤ r → r ≤ 1 → ∃ w∈W, w ≤ ρ*r ∧ ρ*r ≤ Λ*w) →
        ∀ t, IntervalAD ζ dimension
          ((2*(4*Krow^2+3*Krow)+2)*
            ((27:ℝ)^4*(67584000*B*(8*Cband/rate)*Kfill*(8+6*B))*Λ))
          (p.zoomScalarSet A ρ center F t) := by
  classical
  have hb : 0 < b := by rw [hb_eq]; positivity
  obtain ⟨U0,hU0,hloss0,hE0,hfull0,hpos0,htables⟩ :=
    p.original_hereditary_table_preparation_resolved (I:=W) μ E hE hfull hε hθ hKcensus hθK
      hCband hrate hcensus steps hsteps
      (by rw [←hb_eq]; exact hbρ.trans hρ1) (by rw [←hb_eq]; exact hbρ.trans hρθ)
      (fun w => fineSteps w) (by
        intro w
        rw [←hb_eq,←hwidth w w.property]
        exact (hwρ w w.property).trans hρ1) (by
        intro w
        rw [←hb_eq,←hwidth w w.property]
        exact (hwρ w w.property).trans hρθ) reference href hreftop hband
  simp only [←hb_eq] at hloss0 hE0 hfull0 hpos0 htables
  let R0 := (p.physicalState b) ⁻¹' U0
  let μ0 := μ.restrict R0
  let E0 := E ∩ R0
  have hE0p : E0 ⊆ p.event := inter_subset_left.trans hEp
  obtain ⟨row,hrow,hrowB,hrowfit,U1,hU1,hloss1,hprior,hpositive⟩ :=
    p.exists_original_strip_preparation_with_budget (I:=W) ν hκ hH hjets μ0 field hE0
      hE0p hfull0 ρ b B error L Hprior hρ hρ1 hb hbρ (zero_le_one.trans hB) he hL
      hHprior (fun w => w) (fun w => hb.trans_le (hbw w w.property))
      (fun w => hround w w.property) (fun w => hgraphWidth w w.property)
      (fun w => hrowWidth w w.property)
      (fun z hz => hbound z hz.1) (fun z hz z' hz' => hcompare z hz.1 z' hz'.1)
      (fun z hz => hgraph z hz.1)
  let R1 := (p.physicalState b) ⁻¹' U1
  let current := μ0.restrict R1
  have hpencil0 := p.pencil_bound_under_whole_state_cut μ b δ failure U0 hpencil
  have hpencil1 := p.pencil_bound_under_whole_state_cut μ0 b δ failure U1 hpencil0
  have hR1 : MeasurableSet R1 := (p.measurable_physicalState b) hU1
  have hcurfull : ∀ᵐ z ∂current, z∈E0 := ae_mono Measure.restrict_le_self hfull0
  have hcurdom : current ≤ Kden • (p.prior ν).prod volume :=
    Measure.restrict_le_self.trans (Measure.restrict_le_self.trans hdom)
  refine ⟨U0,U1,row,hU0,hU1,hrow,hrowB,?_,?_⟩
  · have hm : μ0 R1=current univ := (Measure.restrict_apply_univ R1).symm
    rw [hm] at hloss1
    have hcard : (Fintype.card W:ℝ)=(W.card:ℝ) := by simp
    rw [hcard] at hloss0 hloss1
    simp only [measure_univ,mul_one] at hloss1
    let loss0 := ENNReal.ofReal ((Kcensus*((2:ℝ)^steps)^3)*((W.card:ℝ)*rate))*reference
    let loss1 := ENNReal.ofReal ((300*7^8*H)*(W.card:ℝ)/Hprior)
    have h0 : μ univ ≤ μ0 univ+loss0 := by
      simpa only [μ0,Measure.restrict_apply_univ,loss0,R0] using hloss0
    have h1 : μ0 univ ≤ current univ+loss1 := hloss1
    change μ univ ≤ current univ+loss1+loss0
    exact h0.trans (add_le_add h1 (le_refl loss0))
  · intro A hA center F ηF ζ Λ Krow hηF hζ hζ1 hΛ hKrow hdiam hF hfit hsmall hscales
    have hAE0 : A ⊆ E0 := fun z hz => (hA hz).1
    have hAE : A ⊆ p.event := hAE0.trans hE0p
    have hη : 0 ≤ ηF+4*L*ρ := by positivity
    apply p.scalar_support_from_original_census ν hκ current Kden hKden E0 A hE0 hE0p hAE
      hcurfull hcurdom center F row W hb hρ hbρ hB hη (by positivity) hKfill
      hdim hdim1 hζ hζ1 hΛ hKrow fineSteps columnSteps hwidth hcolumn hbw hwρ hsmall hdiam
      (fun C j => (norm_le_pi_norm (row C) j).trans (hrowB C)) hF ?_ hscales
      Hprior δ failure Cmk hHprior.le hδ hfailure hfailure1 hCmk hMK hfillBudget ?_ ?_ hpencil1 ?_
    · intro w hw z hz i
      rw [p.stripLabel_coarse]
      have hrowfitz := (norm_le_pi_norm
        (field z-row (roundedPhysicalCode b ρ (p.originalPoint z))) i.succ).trans
          (hrowfit z (hAE0 hz))
      change |field z i.succ-row (roundedPhysicalCode b ρ (p.originalPoint z)) i.succ| ≤ _ at hrowfitz
      change |row (roundedPhysicalCode b ρ (p.originalPoint z)) i.succ-F z.2 i| ≤ _
      apply (abs_sub_le _ (field z i.succ) _).trans
      rw [abs_sub_comm _ (field z i.succ)]
      linarith only [hrowfitz,hfit z hz i]
    · intro w hw z hz
      have hh := hprior ⟨w,hw⟩ z (hA hz).2
      simpa only [measureReal_def,Measure.restrict_apply_univ] using hh
    · intro w hw z hz
      exact hpositive ⟨w,hw⟩ z (hA hz).2
    · intro w hw n hn q
      have hh := htables ⟨w,hw⟩ n
      rw [←hwidth w hw] at hh
      exact hh hn q


/-- Compatibility interface; the actual construction needs only bands
above the original finite resolution. -/
theorem exists_original_scalar_support_preparation (p : PhysicalModel) (ν : Measure Ln)
    [IsProbabilityMeasure (p.prior ν)] (hκ : 1 ≤ p.slack)
    {H : ℝ} (hH : 1 ≤ H)
    (hjets : ∀ l∈p.assigned, |p.scalarCoefficients l 1| ≤ H ∧
      |p.scalarCoefficients l 2| ≤ H ∧ |p.scalarCoefficients l 4| ≤ H ∧
        |p.scalarCoefficients l 6| ≤ H)
    (μ : Measure Ev) [IsFiniteMeasure μ] (Kden : NNReal) (hKden : 0 < Kden)
    (E : Set Ev) (hE : MeasurableSet E) (hEp : E ⊆ p.event)
    (hfull : ∀ᵐ z ∂μ, z∈E) (hdom : μ ≤ Kden • (p.prior ν).prod volume)
    (field : Ev → Fin 3 → ℝ) (W : Finset ℝ)
    {ε θ Kcensus dimension Cband rate b ρ B error L Hprior : ℝ}
    (hε : 0 < ε) (hθ : 0 < θ) (hKcensus : 1 ≤ Kcensus) (hθK : θ ≤ Kcensus)
    (hCband : 0 ≤ Cband) (hrate : 0 < rate)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρθ : ρ ≤ θ)
    (steps : ℕ) (hsteps : Kcensus^(100:ℕ) ≤ (2:ℝ)^steps)
    (hb_eq : b=ε*(2:ℝ)^steps) (hbρ : b ≤ ρ)
    (hB : 1 ≤ B) (he : 0 ≤ error) (hL : 0 ≤ L) (hHprior : 0 < Hprior)
    (fineSteps columnSteps : ℝ → ℕ)
    (hwidth : ∀ w∈W, w=b*(2:ℝ)^(fineSteps w))
    (hcolumn : ∀ w∈W, ρ=w*(2:ℝ)^(columnSteps w))
    (hbw : ∀ w∈W, b ≤ w) (hwρ : ∀ w∈W, w ≤ ρ)
    (hround : ∀ w∈W, (1+3*B)*b ≤ w)
    (hgraphWidth : ∀ w∈W, error*ρ ≤ w)
    (hrowWidth : ∀ w∈W, L*H*ρ^2 ≤ w)
    (hbound : ∀ z∈E, ‖field z‖ ≤ B)
    (hcompare : ∀ z∈E, ∀ z'∈E,
      ‖field z-field z'‖ ≤ L*(‖p.originalPoint z-p.originalPoint z'‖+ρ))
    (hgraph : ∀ z∈E,
      |(p.signal z.1).derivative.eval z.2-∑ j, field z j*p.velocity z.1 j| ≤ error)
    (hcensus : ∀ a w : ℝ, ε ≤ a → a ≤ 1 → ε ≤ w → w ≤ 1 →
      Kcensus^(100:ℕ)*a ≤ θ*w →
        (occupied E (fun x j => p.originalBase x j) (fun x => p.originalPoint x 3/θ) a w).Finite ∧
        ((occupied E (fun x j => p.originalBase x j)
          (fun x => p.originalPoint x 3/θ) a w).ncard:ℝ) ≤ Kcensus/(a^3*w^dimension))
    (reference : ENNReal) (href : 0 < reference) (hreftop : reference ≠ ⊤)
    (hband : ∀ R : ℝ, 0 < R → R ≤ 8*ρ →
      ∀ U : Set P3, MeasurableSet U → ∀ c : P3 → ℝ, Measurable c →
      μ {x | p.originalBase x∈U ∧ |p.originalPoint x 3-c (p.originalBase x)| ≤ R} ≤
        ENNReal.ofReal (Cband*θ^(-dimension)*R^dimension)*reference*volume U)
    (δ failure Cmk Kfill : ℝ) (hδ : 0 < δ) (hfailure : 0 ≤ failure)
    (hfailure1 : failure < 1) (hCmk : 0 ≤ Cmk) (hMK : FiniteMK 3 Cmk)
    (hKfill : 0 < Kfill) (hdim : 0 ≤ dimension) (hdim1 : dimension ≤ 1)
    (hfillBudget : (8*Cmk*7^3)^2*(3*(Kden:ℝ)*Hprior)^3 ≤
      ((δ/2)^3/2*(1-failure)^3)*Kfill)
    (hpencil : ∀ q, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      Module.finrank ℝ V < 3 →
      μ {z | p.physicalState b z=q ∧
        Metric.infDist (NativeAssigned.direction (p.baseVelocityVector z.1)) (V : Set _) < δ} ≤
        ENNReal.ofReal failure*μ ((p.physicalState b) ⁻¹' {q})) :
    ∃ (U0 U1 : Set (Fin 4 → ℤ)) (row : (Fin 4 → ℤ) → Fin 3 → ℝ),
      MeasurableSet U0 ∧ MeasurableSet U1 ∧ Measurable row ∧ (∀ C, ‖row C‖ ≤ B) ∧
      let R0 := (p.physicalState b) ⁻¹' U0
      let R1 := (p.physicalState b) ⁻¹' U1
      let current := (μ.restrict R0).restrict R1
      μ univ ≤ current univ+
        ENNReal.ofReal ((300*7^8*H)*(W.card:ℝ)/Hprior)+
        ENNReal.ofReal ((Kcensus*((2:ℝ)^steps)^3)*((W.card:ℝ)*rate))*reference ∧
      ∀ (A : Set Ev), A ⊆ E ∩ R0 ∩ R1 →
      ∀ (center : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ) (ηF ζ Λ Krow : ℝ),
        0 ≤ ηF → 0 < ζ → ζ ≤ 1 → 1 ≤ Λ → 1 ≤ Krow →
        (∀ z∈A, ∀ i, |p.scalarCoefficients z.1 i-center i| ≤ ρ) →
        (∀ z∈A, ‖F z.2‖ ≤ Krow) →
        (∀ z∈A, ∀ i : Fin 2, |field z i.succ-F z.2 i| ≤ ηF) →
        (∀ w∈W, 4*(ηF+4*L*ρ)*ρ+(1+3*B)*b ≤ w/2) →
        (∀ r : ℝ, ζ ≤ r → r ≤ 1 → ∃ w∈W, w ≤ ρ*r ∧ ρ*r ≤ Λ*w) →
        ∀ t, IntervalAD ζ dimension
          ((2*(4*Krow^2+3*Krow)+2)*
            ((27:ℝ)^4*(67584000*B*(8*Cband/rate)*Kfill*(8+6*B))*Λ))
          (p.zoomScalarSet A ρ center F t) := by
  exact p.exists_original_scalar_support_preparation_resolved ν hκ hH hjets μ Kden hKden E hE hEp hfull hdom
    field W hε hθ hKcensus hθK hCband hrate hρ hρ1 hρθ steps hsteps hb_eq hbρ
    hB he hL hHprior fineSteps columnSteps hwidth hcolumn hbw hwρ hround hgraphWidth hrowWidth
    hbound hcompare hgraph hcensus reference href hreftop
    (fun R hεR hRmax U hU c hcm => hband R (hε.trans_le hεR) hRmax U hU c hcm)
    δ failure Cmk Kfill hδ hfailure hfailure1 hCmk hMK hKfill hdim hdim1 hfillBudget hpencil

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
