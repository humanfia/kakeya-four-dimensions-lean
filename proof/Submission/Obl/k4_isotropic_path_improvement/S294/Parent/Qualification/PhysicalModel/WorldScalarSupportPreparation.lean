-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.WorldScalarSupportPreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.ScalarSupportPreparation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.TimeRow
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FourJetTimeRows

/-! Construct all original coefficient-world time rows and scalar
support estimates from the actual census, strip caps and pencil breadth.
The two preliminary cuts precede every later coefficient-world selection.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set MeasureTheory
open Submission.Lib.K4ParentSignalPreparation.Census
open Submission.Lib.K4ContinuousKakeya
open WangZahlLot.Obl.wz_slab_local_linearity
open scoped ENNReal BigOperators

noncomputable section

def worldScalarSupportConstant (B Cband rate Kfill Lambda : ℝ) : ℝ :=
  (2*(4*B^2+3*B)+2)*
    ((27:ℝ)^4*(67584000*B*(8*Cband/rate)*Kfill*(8+6*B))*Lambda)

/-- The world rows and their scalar supports are produced together.
Every row is measurable; row comparison and support are hereditary on
all later restrictions. No per-world scalar support premise is used. -/
theorem exists_original_world_scalar_support_with_state_cut_resolved (p : PhysicalModel) (ν : Measure Ln)
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
        ENNReal.ofReal failure*μ ((p.physicalState b) ⁻¹' {q}))
    (zeta Lambda : ℝ) (hzeta : 0 < zeta) (hzeta1 : zeta ≤ 1) (hLambda : 1 ≤ Lambda)
    (hworldSmall : ∀ w∈W,
      4*(2*((3*H+1)*L)*ρ+4*L*ρ)*ρ+(1+3*B)*b ≤ w/2)
    (hworldScales : ∀ r : ℝ, zeta ≤ r → r ≤ 1 →
      ∃ w∈W, w ≤ ρ*r ∧ ρ*r ≤ Lambda*w) :
    ∃ (keep : Set Ev) (F : (Fin 7 → ℤ) → ℝ → Fin 2 → ℝ),
      MeasurableSet keep ∧ keep⊆E ∧
      (∃ U : Set (Fin 4 → ℤ), MeasurableSet U ∧ keep=E∩(p.physicalState b) ⁻¹' U) ∧
      μ univ ≤ μ keep+
        ENNReal.ofReal ((300*7^8*H)*(W.card:ℝ)/Hprior)+
        ENNReal.ofReal ((Kcensus*((2:ℝ)^steps)^3)*((W.card:ℝ)*rate))*reference ∧
      (∀ world, Measurable (F world)) ∧
      (∀ z∈keep, ‖F (Jets2.parameterCode ρ (p.scalarCoefficients z.1)) z.2‖ ≤ B) ∧
      (∀ z∈keep,
        ‖F (Jets2.parameterCode ρ (p.scalarCoefficients z.1)) z.2-
          (fun i : Fin 2 => field z i.succ)‖ ≤ 2*((3*H+1)*L)*ρ) ∧
      (∀ z∈keep, ∀ z'∈keep,
        Jets2.parameterCode ρ (p.scalarCoefficients z.1)=
          Jets2.parameterCode ρ (p.scalarCoefficients z'.1) →
        ‖F (Jets2.parameterCode ρ (p.scalarCoefficients z.1)) z.2-
          F (Jets2.parameterCode ρ (p.scalarCoefficients z'.1)) z'.2‖ ≤
          3*((3*H+1)*L)*(|z.2-z'.2|+ρ)) ∧
      ∀ S : Set Ev, S⊆keep → ∀ world t,
        IntervalAD zeta dimension (worldScalarSupportConstant B Cband rate Kfill Lambda)
          {x | ∃ l, (l,t)∈S ∧ Jets2.parameterCode ρ (p.scalarCoefficients l)=world ∧
            Jets2.zS (F world)
              (Jets2.zoomCoefficients ρ (Jets2.parameterCenter ρ world) (p.scalarCoefficients l)) t=x} := by
  obtain ⟨U0,U1,row,hU0,hU1,hrow,hrowBound,hmass,hSS⟩ :=
    p.exists_original_scalar_support_preparation_resolved ν hκ hH hjets μ Kden hKden E hE hEp hfull hdom
      field W hε hθ hKcensus hθK hCband hrate hρ hρ1 hρθ steps hsteps hb_eq hbρ
      hB he hL hHprior fineSteps columnSteps hwidth hcolumn hbw hwρ hround
      hgraphWidth hrowWidth hbound hcompare hgraph hcensus reference href hreftop hband
      δ failure Cmk Kfill hδ hfailure hfailure1 hCmk hMK hKfill hdim hdim1 hfillBudget hpencil
  let R0 := (p.physicalState b) ⁻¹' U0
  let R1 := (p.physicalState b) ⁻¹' U1
  let keep := (E∩R0)∩R1
  have hR0 : MeasurableSet R0 := (p.measurable_physicalState b) hU0
  have hR1 : MeasurableSet R1 := (p.measurable_physicalState b) hU1
  have hkeep : MeasurableSet keep := (hE.inter hR0).inter hR1
  have hkeepE : keep⊆E := fun z hz => hz.1.1
  have hkeepMass : μ keep=((μ.restrict R0).restrict R1) univ := by
    rw [Measure.restrict_apply_univ,Measure.restrict_apply hR1]
    apply measure_congr
    filter_upwards [hfull] with z hz
    simp only [keep,mem_inter_iff,hz,true_and]
    apply propext
    tauto
  let tangential : Ev → Fin 2 → ℝ := fun z i => field z i.succ
  have hdrop (z z' : Ev) : ‖tangential z-tangential z'‖ ≤ ‖field z-field z'‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    exact norm_le_pi_norm (field z-field z') i.succ
  have htBound (z : Ev) (hz : z∈keep) : ‖tangential z‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hbound z (hkeepE hz)))).mpr
    intro i
    exact (norm_le_pi_norm (field z) i.succ).trans (hbound z (hkeepE hz))
  obtain ⟨F,hFm,hFb,hFfit,hFcmp⟩ := Jets2.exists_canonical_world_time_rows_of_jets keep
    p.scalarCoefficients tangential ρ H B L hρ hH hL
    (fun z hz => p.event_time z (hEp (hkeepE hz)))
    (fun z hz => hjets z.1 (p.event_assignment z (hEp (hkeepE hz)))) htBound (by
      intro z hz z' hz' _
      exact (hdrop z z').trans ((hcompare z (hkeepE hz) z' (hkeepE hz')).trans
        (mul_le_mul_of_nonneg_left
          (add_le_add (p.physical_norm_le_scalar_position_norm z z') le_rfl) hL)))
  refine ⟨keep,F,hkeep,hkeepE,?_,?_,hFm,hFb,hFfit,hFcmp,?_⟩
  · refine ⟨U0∩U1,hU0.inter hU1,?_⟩
    ext z
    simp only [keep,R0,R1,mem_inter_iff,mem_preimage]
    tauto
  · dsimp only [R0,R1] at hkeepMass
    rwa [←hkeepMass] at hmass
  · intro S hS world t
    let A := {z : Ev | z∈S ∧ Jets2.parameterCode ρ (p.scalarCoefficients z.1)=world}
    have hA : A⊆E∩R0∩R1 := fun z hz => hS hz.1
    have hworld (z : Ev) (hz : z∈A) :
        Jets2.parameterCode ρ (p.scalarCoefficients z.1)=world := hz.2
    have hs := hSS A hA (Jets2.parameterCenter ρ world) (F world)
      (2*((3*H+1)*L)*ρ) zeta Lambda B (by positivity) hzeta hzeta1 hLambda hB
      (by
        intro z hz i
        simpa only [hworld z hz] using
          Jets2.original_parameter_center_distance ρ hρ (p.scalarCoefficients z.1) i)
      (by
        intro z hz
        simpa only [hworld z hz] using hFb z (hS hz.1))
      (by
        intro z hz i
        have hf := (norm_le_pi_norm _ i).trans (hFfit z (hS hz.1))
        have hf' : |F world z.2 i-field z i.succ| ≤ 2*((3*H+1)*L)*ρ := by
          simpa only [hworld z hz,tangential,Pi.sub_apply,Real.norm_eq_abs] using hf
        simpa only [abs_sub_comm] using hf')
      hworldSmall hworldScales t
    simpa only [worldScalarSupportConstant,zoomScalarSet,A,mem_ofPred_eq,and_assoc] using hs


/-- The all-positive-radius interface is preserved as a wrapper. -/
theorem exists_original_world_scalar_support_with_state_cut (p : PhysicalModel) (ν : Measure Ln)
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
        ENNReal.ofReal failure*μ ((p.physicalState b) ⁻¹' {q}))
    (zeta Lambda : ℝ) (hzeta : 0 < zeta) (hzeta1 : zeta ≤ 1) (hLambda : 1 ≤ Lambda)
    (hworldSmall : ∀ w∈W,
      4*(2*((3*H+1)*L)*ρ+4*L*ρ)*ρ+(1+3*B)*b ≤ w/2)
    (hworldScales : ∀ r : ℝ, zeta ≤ r → r ≤ 1 →
      ∃ w∈W, w ≤ ρ*r ∧ ρ*r ≤ Lambda*w) :
    ∃ (keep : Set Ev) (F : (Fin 7 → ℤ) → ℝ → Fin 2 → ℝ),
      MeasurableSet keep ∧ keep⊆E ∧
      (∃ U : Set (Fin 4 → ℤ), MeasurableSet U ∧ keep=E∩(p.physicalState b) ⁻¹' U) ∧
      μ univ ≤ μ keep+
        ENNReal.ofReal ((300*7^8*H)*(W.card:ℝ)/Hprior)+
        ENNReal.ofReal ((Kcensus*((2:ℝ)^steps)^3)*((W.card:ℝ)*rate))*reference ∧
      (∀ world, Measurable (F world)) ∧
      (∀ z∈keep, ‖F (Jets2.parameterCode ρ (p.scalarCoefficients z.1)) z.2‖ ≤ B) ∧
      (∀ z∈keep,
        ‖F (Jets2.parameterCode ρ (p.scalarCoefficients z.1)) z.2-
          (fun i : Fin 2 => field z i.succ)‖ ≤ 2*((3*H+1)*L)*ρ) ∧
      (∀ z∈keep, ∀ z'∈keep,
        Jets2.parameterCode ρ (p.scalarCoefficients z.1)=
          Jets2.parameterCode ρ (p.scalarCoefficients z'.1) →
        ‖F (Jets2.parameterCode ρ (p.scalarCoefficients z.1)) z.2-
          F (Jets2.parameterCode ρ (p.scalarCoefficients z'.1)) z'.2‖ ≤
          3*((3*H+1)*L)*(|z.2-z'.2|+ρ)) ∧
      ∀ S : Set Ev, S⊆keep → ∀ world t,
        IntervalAD zeta dimension (worldScalarSupportConstant B Cband rate Kfill Lambda)
          {x | ∃ l, (l,t)∈S ∧ Jets2.parameterCode ρ (p.scalarCoefficients l)=world ∧
            Jets2.zS (F world)
              (Jets2.zoomCoefficients ρ (Jets2.parameterCenter ρ world) (p.scalarCoefficients l)) t=x} := by
  exact p.exists_original_world_scalar_support_with_state_cut_resolved ν hκ hH hjets μ Kden hKden E hE hEp hfull hdom
    field W hε hθ hKcensus hθK hCband hrate hρ hρ1 hρθ steps hsteps hb_eq hbρ
    hB he hL hHprior fineSteps columnSteps hwidth hcolumn hbw hwρ hround hgraphWidth hrowWidth
    hbound hcompare hgraph hcensus reference href hreftop
    (fun R hεR hRmax U hU c hcm => hband R (hε.trans_le hεR) hRmax U hU c hcm)
    δ failure Cmk Kfill hδ hfailure hfailure1 hCmk hMK hKfill hdim hdim1 hfillBudget hpencil
    zeta Lambda hzeta hzeta1 hLambda hworldSmall hworldScales


/-- The original scalar-support interface, forgetting only the displayed
whole-fine-state cut. -/
theorem exists_original_world_scalar_support (p : PhysicalModel) (ν : Measure Ln)
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
        ENNReal.ofReal failure*μ ((p.physicalState b) ⁻¹' {q}))
    (zeta Lambda : ℝ) (hzeta : 0 < zeta) (hzeta1 : zeta ≤ 1) (hLambda : 1 ≤ Lambda)
    (hworldSmall : ∀ w∈W,
      4*(2*((3*H+1)*L)*ρ+4*L*ρ)*ρ+(1+3*B)*b ≤ w/2)
    (hworldScales : ∀ r : ℝ, zeta ≤ r → r ≤ 1 →
      ∃ w∈W, w ≤ ρ*r ∧ ρ*r ≤ Lambda*w) :
    ∃ (keep : Set Ev) (F : (Fin 7 → ℤ) → ℝ → Fin 2 → ℝ),
      MeasurableSet keep ∧ keep⊆E ∧
      μ univ ≤ μ keep+
        ENNReal.ofReal ((300*7^8*H)*(W.card:ℝ)/Hprior)+
        ENNReal.ofReal ((Kcensus*((2:ℝ)^steps)^3)*((W.card:ℝ)*rate))*reference ∧
      (∀ world, Measurable (F world)) ∧
      (∀ z∈keep, ‖F (Jets2.parameterCode ρ (p.scalarCoefficients z.1)) z.2‖ ≤ B) ∧
      (∀ z∈keep,
        ‖F (Jets2.parameterCode ρ (p.scalarCoefficients z.1)) z.2-
          (fun i : Fin 2 => field z i.succ)‖ ≤ 2*((3*H+1)*L)*ρ) ∧
      (∀ z∈keep, ∀ z'∈keep,
        Jets2.parameterCode ρ (p.scalarCoefficients z.1)=
          Jets2.parameterCode ρ (p.scalarCoefficients z'.1) →
        ‖F (Jets2.parameterCode ρ (p.scalarCoefficients z.1)) z.2-
          F (Jets2.parameterCode ρ (p.scalarCoefficients z'.1)) z'.2‖ ≤
          3*((3*H+1)*L)*(|z.2-z'.2|+ρ)) ∧
      ∀ S : Set Ev, S⊆keep → ∀ world t,
        IntervalAD zeta dimension (worldScalarSupportConstant B Cband rate Kfill Lambda)
          {x | ∃ l, (l,t)∈S ∧ Jets2.parameterCode ρ (p.scalarCoefficients l)=world ∧
            Jets2.zS (F world)
              (Jets2.zoomCoefficients ρ (Jets2.parameterCenter ρ world) (p.scalarCoefficients l)) t=x} := by
  obtain ⟨keep,F,hkeep,hkeepE,_hstateCut,hmass,hFm,hFb,hFfit,hFcmp,hSS⟩ :=
    p.exists_original_world_scalar_support_with_state_cut ν hκ hH hjets μ Kden hKden E hE hEp hfull hdom
      field W hε hθ hKcensus hθK hCband hrate hρ hρ1 hρθ steps hsteps hb_eq hbρ
      hB he hL hHprior fineSteps columnSteps hwidth hcolumn hbw hwρ hround
      hgraphWidth hrowWidth hbound hcompare hgraph hcensus reference href hreftop hband
      δ failure Cmk Kfill hδ hfailure hfailure1 hCmk hMK hKfill hdim hdim1 hfillBudget hpencil
      zeta Lambda hzeta hzeta1 hLambda hworldSmall hworldScales
  exact ⟨keep,F,hkeep,hkeepE,hmass,hFm,hFb,hFfit,hFcmp,hSS⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
