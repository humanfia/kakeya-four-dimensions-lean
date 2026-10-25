-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.RowWorldSupportPreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph.PositivePhysicalRowRegularity
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.RowBreadthFromStrips
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.WorldScalarSupportPreparation

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set MeasureTheory
open Submission.Lib.K4ParentSignalPreparation.Census
open Submission.Lib.K4ContinuousKakeya
open Submission.Lib.K4ThreeBaseRows
open Submission.Lib.K4ThreeBaseRows.RowBinLists (rowEval vbin)
open Submission.Lib.K4CommonLocalChoice (cell)
open WangZahlLot.Obl.wz_slab_local_linearity
open scoped ENNReal BigOperators RealInnerProductSpace

noncomputable section

/-- Construct row regularity and every coefficient-world scalar support
on ONE union of original fine states. All breadth, census and moving
band hypotheses refer to the preceding actual current incidence law. -/
theorem prepare_original_row_world_support (p : PhysicalModel) (ν : Measure Ln)
    [IsProbabilityMeasure (p.prior ν)] (hκ : 1 ≤ p.slack)
    (μ : Measure Ev) [IsFiniteMeasure μ] (Kden : NNReal) (hKden : 0 < Kden)
    (E : Set Ev) (hE : MeasurableSet E) (hEp : E ⊆ p.event)
    (hfull : ∀ᵐ z ∂μ, z∈E) (hdom : μ ≤ Kden • (p.prior ν).prod volume)
    (G : (Fin 4 → ℤ) → Fin 3 → ℝ)
    {b ρ H B error Lp Uvelocity stripWidth radius failure : ℝ}
    (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbρ : b ≤ ρ)
    (hH : 1 ≤ H) (hB : 1 ≤ B) (he : 0 ≤ error) (hLp : 0 ≤ Lp)
    (hjets : ∀ l∈p.assigned, |p.scalarCoefficients l 1| ≤ H ∧
      |p.scalarCoefficients l 2| ≤ H ∧ |p.scalarCoefficients l 4| ≤ H ∧
        |p.scalarCoefficients l 6| ≤ H)
    (hG : ∀ z∈E, ∀ j, |G (p.physicalState b z) j| ≤ B)
    (hvel : ∀ z∈E, ∀ j, |Graph.planarVel p z.1 j| ≤ B)
    (hgraph : ∀ z∈E, |(p.signal z.1).derivative.eval z.2-
      ∑ j, G (p.physicalState b z) j*p.velocity z.1 j| ≤ error)
    (hUvelocity : 0 ≤ Uvelocity) (hfailure : 0 ≤ failure) (hfailure1 : failure < 1)
    (hvelocity : ∀ᵐ z ∂μ, ‖p.planarVelocityVector z.1‖ ≤ Uvelocity)
    (hstrip : ∀ q (normal : EuclideanSpace ℝ (Fin 2)) offset, ‖normal‖=1 →
      μ {z | p.physicalState b z=q ∧
        |inner ℝ normal (p.planarVelocityVector z.1)-offset| ≤ stripWidth} ≤
          ENNReal.ofReal failure*μ ((p.physicalState b) ⁻¹' {q}))
    (regLength : ℕ) (hregLength : 1 ≤ regLength) (regScale : ℕ → ℝ)
    (hreg0 : regScale 0=1) (hregPos : ∀ i, 0 < regScale i)
    (hbreg : ∀ i < regLength, b ≤ regScale i)
    (Ar : ℝ) (hAr : 1 ≤ Ar)
    (hregRatio : ∀ i, i+1 < regLength → regScale i ≤ Ar*regScale (i+1))
    (hregFloor : regScale (regLength-1) ≤ ρ)
    (hregNest : ∀ i < regLength, ∀ x∈E, ∀ z∈E,
      p.physicalState b x=p.physicalState b z →
        cell (regScale i) (Graph.physX p x)=cell (regScale i) (Graph.physX p z))
    (regWeight : ℕ → (Fin 2 → ℤ) → ℝ) (velocityBins : ℕ → Finset (Fin 2 → ℤ))
    (derivativeLists : ℕ → (Fin 4 → ℤ) → (Fin 2 → ℤ) → Finset ℤ)
    (rhoBroad D KL Areg P : ℝ) (hBroadRadius : 0 < rhoBroad)
    (hBroadSmall : rhoBroad ≤ 1/4) (hBroadWidth : 2*(Uvelocity+1)*rhoBroad ≤ stripWidth)
    (hD : 0 < D) (hAreg : 1 ≤ Areg) (hBA : B ≤ Areg) (hKLA : KL ≤ Areg)
    (hDA : D ≤ Areg) (hcA : (1-failure)⁻¹ ≤ Areg) (hρA : rhoBroad⁻¹ ≤ Areg)
    (heA : ∀ i < regLength, error/regScale i ≤ Areg)
    (hweight : ∀ i v, 0 ≤ regWeight i v)
    (hP : ∀ i < regLength, ∑ v∈velocityBins i, regWeight i v ≤ P)
    (hderiv : ∀ i < regLength, ∀ z∈E,
      ⌊Graph.physRate p z/regScale i⌋∈derivativeLists i
        (cell (regScale i) (Graph.physX p z)) (vbin (regScale i) (Graph.planarVel p z.1)))
    (hderivCard : ∀ i < regLength, ∀ q v, ((derivativeLists i q v).card:ℝ) ≤ KL)
    (hvelocityBins : ∀ i < regLength, ∀ z∈E,
      vbin (regScale i) (Graph.planarVel p z.1)∈velocityBins i)
    (hstateDom : ∀ i < regLength, ∀ z∈E, ∀ v,
      μ.real (E∩(p.physicalState b) ⁻¹' {p.physicalState b z}∩
        {x | vbin (regScale i) (Graph.planarVel p x.1)=v}) ≤
          D*μ.real (E∩(p.physicalState b) ⁻¹' {p.physicalState b z})*regWeight i v)
    (hLpReg : 6*(Ar+3*B) ≤ Lp)
    (W : Finset ℝ) {resolution Kcensus dimension Cband rate Hprior : ℝ}
    (hresolution : 0 < resolution) (hKcensus : 1 ≤ Kcensus) (hCband : 0 ≤ Cband)
    (hrate : 0 < rate) (hHprior : 0 < Hprior)
    (steps : ℕ) (hsteps : Kcensus^(100:ℕ) ≤ (2:ℝ)^steps)
    (hb_eq : b=resolution*(2:ℝ)^steps)
    (fineSteps columnSteps : ℝ → ℕ)
    (hwidth : ∀ w∈W, w=b*(2:ℝ)^(fineSteps w))
    (hcolumn : ∀ w∈W, ρ=w*(2:ℝ)^(columnSteps w))
    (hbw : ∀ w∈W, b ≤ w) (hwρ : ∀ w∈W, w ≤ ρ)
    (hround : ∀ w∈W, (1+3*B)*b ≤ w)
    (hgraphWidth : ∀ w∈W, error*ρ ≤ w)
    (hrowWidth : ∀ w∈W, Lp*H*ρ^2 ≤ w)
    (hcensus : ∀ a w : ℝ, resolution ≤ a → a ≤ 1 → resolution ≤ w → w ≤ 1 →
      Kcensus^(100:ℕ)*a ≤ w →
        (occupied E (fun z j => p.originalBase z j) (fun z => p.originalPoint z 3) a w).Finite ∧
        ((occupied E (fun z j => p.originalBase z j) (fun z => p.originalPoint z 3) a w).ncard:ℝ) ≤
          Kcensus/(a^3*w^dimension))
    (hband : ∀ R : ℝ, resolution ≤ R → R ≤ 8*ρ →
      ∀ U : Set P3, MeasurableSet U → ∀ center : P3 → ℝ, Measurable center →
      μ {z | p.originalBase z∈U ∧ |p.originalPoint z 3-center (p.originalBase z)| ≤ R} ≤
        ENNReal.ofReal (Cband*R^dimension)*volume U)
    (Cmk Kfill : ℝ) (hradius : 0 < radius) (hCmk : 0 ≤ Cmk) (hMK : FiniteMK 3 Cmk)
    (hKfill : 0 < Kfill) (hdim : 0 ≤ dimension) (hdim1 : dimension ≤ 1)
    (hfillBudget : (8*Cmk*7^3)^2*(3*(Kden:ℝ)*Hprior)^3 ≤
      ((radius/2)^3/2*(1-failure)^3)*Kfill)
    (hPencilWidth : 2*(Uvelocity+1)*((Uvelocity+1)*radius) ≤ stripWidth)
    (hPencilSmall : (Uvelocity+1)*radius ≤ 1/4)
    (zeta Lambda : ℝ) (hzeta : 0 < zeta) (hzeta1 : zeta ≤ 1) (hLambda : 1 ≤ Lambda)
    (hworldSmall : ∀ w∈W,
      4*(2*((3*H+1)*Lp)*ρ+4*Lp*ρ)*ρ+(1+3*B)*b ≤ w/2)
    (hworldScales : ∀ r : ℝ, zeta ≤ r → r ≤ 1 → ∃ w∈W, w ≤ ρ*r ∧ ρ*r ≤ Lambda*w) :
    ∃ (U : Set (Fin 4 → ℤ)) (F : (Fin 7 → ℤ) → ℝ → Fin 2 → ℝ), MeasurableSet U ∧
      let keep := E∩(p.physicalState b) ⁻¹' U
      MeasurableSet keep ∧
      μ univ ≤ (∏ i∈Finset.range regLength,
        ((4:ENNReal)^4*((7:ℕ)^4*⌊10^10*Areg^27*(P^3+1)⌋₊)))*
        (μ keep+ENNReal.ofReal ((300*7^8*H)*(W.card:ℝ)/Hprior)+
          ENNReal.ofReal ((Kcensus*((2:ℝ)^steps)^3)*((W.card:ℝ)*rate))) ∧
      (∀ z∈keep, ∀ z'∈keep, ‖G (p.physicalState b z)-G (p.physicalState b z')‖ ≤
        Lp*(‖p.originalPoint z-p.originalPoint z'‖+ρ)) ∧
      (∀ world, Measurable (F world)) ∧
      (∀ z∈keep, ‖F (Jets2.parameterCode ρ (p.scalarCoefficients z.1)) z.2‖ ≤ B) ∧
      (∀ z∈keep,
        ‖F (Jets2.parameterCode ρ (p.scalarCoefficients z.1)) z.2-
          (fun i : Fin 2 => G (p.physicalState b z) i.succ)‖ ≤ 2*((3*H+1)*Lp)*ρ) ∧
      (∀ z∈keep, ∀ z'∈keep,
        Jets2.parameterCode ρ (p.scalarCoefficients z.1)=Jets2.parameterCode ρ (p.scalarCoefficients z'.1) →
        ‖F (Jets2.parameterCode ρ (p.scalarCoefficients z.1)) z.2-
          F (Jets2.parameterCode ρ (p.scalarCoefficients z'.1)) z'.2‖ ≤
          3*((3*H+1)*Lp)*(|z.2-z'.2|+ρ)) ∧
      ∀ S : Set Ev, S⊆keep → ∀ world t,
        IntervalAD zeta dimension (worldScalarSupportConstant B Cband rate Kfill Lambda)
          {x | ∃ l, (l,t)∈S ∧ Jets2.parameterCode ρ (p.scalarCoefficients l)=world ∧
            Jets2.zS (F world)
              (Jets2.zoomCoefficients ρ (Jets2.parameterCenter ρ world) (p.scalarCoefficients l)) t=x} := by
  have hBroad := p.row_breadth_of_current_strip_caps μ E hE hfull hUvelocity
    hBroadRadius.le hBroadWidth hBroadSmall hfailure hvelocity hstrip
  have hgraphReg : ∀ z∈E, |Graph.physRate p z-rowEval (G (p.physicalState b z))
      (Graph.planarVel p z.1)| ≤ error := by
    intro z hz
    have hh := hgraph z hz
    rw [←p.scalar_x_derivative] at hh
    simp only [Fin.sum_univ_three,PhysicalModel.velocity,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,mul_one] at hh
    simpa only [Graph.physRate,rowEval,Graph.planarVel,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using hh
  obtain ⟨Ureg,hUreg,hregMass,hregLip⟩ := Graph.physical_row_regularity_with_null_cells p hκ
    μ E hE hEp hfull hb hbρ G regLength hregLength regScale hreg0 hregPos hbreg hAr
    hregRatio hregFloor hregNest regWeight velocityBins derivativeLists hBroadRadius
    (zero_le_one.trans hB) he (by linarith) hD hAreg hBA hKLA hDA hcA hρA heA hweight hP
    hG hvel hgraphReg hderiv hderivCard hvelocityBins hstateDom (fun z _ => hBroad (p.physicalState b z))
  let R := (p.physicalState b) ⁻¹' Ureg
  let Ereg := E∩R
  have hR : MeasurableSet R := (p.measurable_physicalState b) hUreg
  have hEreg : MeasurableSet Ereg := hE.inter hR
  have hregFull : ∀ᵐ z ∂(μ.restrict R), z∈Ereg := by
    filter_upwards [ae_mono Measure.restrict_le_self hfull,ae_restrict_mem hR] with z hz hzr
    exact ⟨hz,hzr⟩
  have hfieldBound : ∀ z∈Ereg, ‖G (p.physicalState b z)‖ ≤ B := by
    intro z hz
    exact Jets2.norm_le_of_abs_le (zero_le_one.trans hB) (hG z hz.1)
  have hfieldLip : ∀ z∈Ereg, ∀ z'∈Ereg,
      ‖G (p.physicalState b z)-G (p.physicalState b z')‖ ≤
        Lp*(‖p.originalPoint z-p.originalPoint z'‖+ρ) := by
    intro z hz z' hz'
    exact (hregLip z hz.1 hz.2 z' hz'.1 hz'.2).trans
      (mul_le_mul_of_nonneg_right hLpReg (by positivity))
  have hcensusReg : ∀ a w : ℝ, resolution ≤ a → a ≤ 1 → resolution ≤ w → w ≤ 1 →
      Kcensus^(100:ℕ)*a ≤ (1:ℝ)*w →
      (occupied Ereg (fun z j => p.originalBase z j) (fun z => p.originalPoint z 3/1) a w).Finite ∧
      ((occupied Ereg (fun z j => p.originalBase z j) (fun z => p.originalPoint z 3/1) a w).ncard:ℝ) ≤
        Kcensus/(a^3*w^dimension) := by
    intro a w ha ha1 hw hw1 hshape
    obtain ⟨hfinite,hcount⟩ := hcensus a w ha ha1 hw hw1 (by simpa only [one_mul] using hshape)
    simp only [div_one]
    have hsub : occupied Ereg (fun z j => p.originalBase z j) (fun z => p.originalPoint z 3) a w ⊆
        occupied E (fun z j => p.originalBase z j) (fun z => p.originalPoint z 3) a w := by
      rintro q ⟨z,hz,hq⟩
      exact ⟨z,hz.1,hq⟩
    exact ⟨hfinite.subset hsub,(show (↑((occupied Ereg (fun z j => p.originalBase z j)
      (fun z => p.originalPoint z 3) a w).ncard):ℝ) ≤
        (↑((occupied E (fun z j => p.originalBase z j) (fun z => p.originalPoint z 3) a w).ncard):ℝ)
        from Nat.cast_le.mpr (ncard_le_ncard hsub hfinite)).trans hcount⟩
  have hpencil := p.pencil_bound_of_current_strip_caps μ hUvelocity hradius.le hPencilWidth
    hPencilSmall hvelocity hstrip
  obtain ⟨keep,F,hkeep,hkeepEreg,⟨Uss,hUss,hwhole⟩,hmass,hFm,hFb,hfit,hRC,hSS⟩ :=
    p.exists_original_world_scalar_support_with_state_cut_resolved ν hκ hH hjets
      (μ.restrict R) Kden hKden Ereg hEreg (fun z hz => hEp hz.1) hregFull
      (Measure.restrict_le_self.trans hdom) (fun z => G (p.physicalState b z)) W
      hresolution (by norm_num) hKcensus hKcensus hCband hrate hρ hρ1 hρ1 steps hsteps hb_eq hbρ
      hB he hLp hHprior fineSteps columnSteps hwidth hcolumn hbw hwρ hround hgraphWidth hrowWidth
      hfieldBound hfieldLip (fun z hz => hgraph z hz.1) hcensusReg 1 (by norm_num) (by norm_num)
      (by
        intro radius' hres hrad U hU center hcenter
        apply (show (μ.restrict R) _ ≤ μ _ from Measure.restrict_le_self _).trans
        simpa only [Real.one_rpow,mul_one] using hband radius' hres hrad U hU center hcenter)
      radius failure Cmk Kfill hradius hfailure hfailure1 hCmk hMK hKfill hdim hdim1 hfillBudget
      (p.pencil_bound_under_whole_state_cut μ b radius failure Ureg hpencil)
      zeta Lambda hzeta hzeta1 hLambda hworldSmall hworldScales
  let U := Ureg∩Uss
  have hwholeE : keep=E∩(p.physicalState b) ⁻¹' U := by
    rw [hwhole]
    ext z
    simp only [Ereg,R,U,mem_inter_iff,mem_preimage]
    tauto
  have hkeepR : keep⊆R := fun z hz => (hkeepEreg hz).2
  have hkeepMass : (μ.restrict R) keep=μ keep := by
    rw [Measure.restrict_apply hkeep,inter_eq_left.mpr hkeepR]
  refine ⟨U,F,hUreg.inter hUss,?_,?_,?_,hFm,?_,?_,?_,?_⟩
  · simpa only [←hwholeE] using hkeep
  · rw [←hwholeE]
    apply hregMass.trans (mul_le_mul' le_rfl ?_)
    simpa only [Measure.restrict_apply_univ,hkeepMass,mul_one] using hmass
  · rw [←hwholeE]
    exact fun z hz z' hz' => hfieldLip z (hkeepEreg hz) z' (hkeepEreg hz')
  · simpa only [←hwholeE] using hFb
  · simpa only [←hwholeE] using hfit
  · simpa only [←hwholeE] using hRC
  · simpa only [←hwholeE] using hSS

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
