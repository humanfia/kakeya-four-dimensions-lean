-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeRootSupplyFromData, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalRootSupply
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeRootPreparation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestorOriginalFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeAncestorVelocityRatios
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeVelocityReference

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData)
open Parent.Qualification
open Parent.Qualification.PhysicalModel
open Parent.Qualification.PhysicalModel.NativeAncestor
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal BigOperators RealInnerProductSpace

noncomputable section

local instance nativeRootSupplyOptionMeasurableSpace (C : ℕ) : MeasurableSpace (Option (Fin C)) := ⊤
local instance nativeRootSupplyOptionMeasurableSingletonClass (C : ℕ) :
    MeasurableSingletonClass (Option (Fin C)) := ⟨fun _ => trivial⟩

/-- Actual native P1 metadata, P5 graph ratios and original census/pure
numerators fill the complete root input. All clock conversion, current
denominators, carriers, canonical caps and prior floors are internal. -/
def nativeRootSupply_of_original_data
    {d : ProblemData} (hd : d.Valid) {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (root : Fin p.C) {Vmax : ℝ} (hVmax : 0 ≤ Vmax)
    (source : Set Ev) (hsource : MeasurableSet source) (hsourceF : source⊆p.F root)
    (hR : (p.R root).totalDegree ≤ 2) (hvelocity : ∀ z∈source, ‖Parent.v z.1‖ ≤ Vmax)
    (S : Set Ev) (hS : MeasurableSet S) (hSsource : S⊆source)
    (scales : OriginalRootScales)
    (hcoeffH : coefficientBound (p:=p) Vmax ≤ scales.H) (hVmaxU : Vmax ≤ scales.Uvelocity)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (hrow : ∀ cd j, |row cd j| ≤ scales.B)
    (hfit : ∀ x∈S,
      |((((2:ℝ)^p.T (p.lev root))⁻¹)/δ (d.N k) (p.r (p.lev root)))*
        Submission.Lib.K4GlobalParentSignal.rate (p.R root) x.1 x.2-
          ∑ j, row (clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) scales.b x) j*
            (![1,Parent.v x.1 0,Parent.v x.1 1] : Fin 3 → ℝ) j| ≤ scales.error)
    (palette : Measure (Fin 2 → ℝ))
    (floors : Jets2.OriginalDyadicFloorData ((hp.frozenPacket root).prior (d.ν k (p.γ root)))
      (coefficientTable (d.N k) p root Vmax) ((hp.frozenPacket root).selectedEvent S)
        palette scales.dimension scales.floorExponent scales.floorStart scales.floorCount)
    (tables : Jets2.OriginalDerivativeListData (coefficientTable (d.N k) p root Vmax)
      ((hp.frozenPacket root).selectedEvent S)
      (fun i : Fin scales.regLength => scales.regLevel i.val) (fun _ => scales.KL))
    (pairPalette : Measure (ℤ×ℤ)) (finePv recordRadius : ℝ) (stripCoeff paletteCoeff : ENNReal)
    (ratios : GraphRecordRatios p (d.N k) root scales.b finePv recordRadius scales.stripWidth
      stripCoeff paletteCoeff ((d.ν k (p.γ root)).prod volume) S pairPalette)
    (hstripCoeff : stripCoeff ≤ ENNReal.ofReal scales.failure)
    (hpaletteCoeff : 4*paletteCoeff ≤ ENNReal.ofReal scales.incidence.Cstate)
    (reference : Jets2.CommonDyadicVelocityReference finePv scales.paletteFinest
      (fun b => (pairPalette.map Parent.OriginalVelocityPalette.palettePairVector) {b}) palette)
    (hfinePv : 0 < finePv) (hfineWidth : finePv ≤ Jets2.dyadicParameterWidth scales.paletteFinest)
    (hpure : ∀ query : ℕ, query ≤ scales.paletteFinest →
      ∀ w : ℝ, scales.resolution ≤ w → w ≤ 1 →
      ∀ (base : Fin 3 → ℤ) (hidden : ℤ) (D : Set (Fin 2 → ℤ)), MeasurableSet D →
      (((d.ν k (p.γ root)).prod volume).restrict S) {z |
        (fun l => ⌊unshearedPacketBase p root z l/scales.resolution⌋)=base ∧
        ⌊physicalParentSignal (d.N k) p root (p.R root) z/w⌋=hidden ∧
        Jets2.parameterCode (Jets2.dyadicParameterWidth query) (fun l => Parent.v z.1 l)∈D} ≤
      (ENNReal.ofReal (scales.Cpure*scales.resolution^3*w^scales.dimension)*
        (palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth query))) D)*
          (ENNReal.ofReal ((hp.frozenPacket root).unitFrame.q)*d.ν k (p.γ root) (p.A root)))
    (hcensus : ∀ a w : ℝ, scales.resolution ≤ a → a ≤ 1 → scales.resolution ≤ w → w ≤ 1 →
      scales.Kcensus^(100:ℕ)*a ≤ w →
      (occupied S (fun z j => unshearedPacketBase p root z j)
        (physicalParentSignal (d.N k) p root (p.R root)) a w).Finite ∧
      ((occupied S (fun z j => unshearedPacketBase p root z j)
        (physicalParentSignal (d.N k) p root (p.R root)) a w).ncard:ℝ) ≤
          scales.Kcensus/(a^3*w^scales.dimension))
    (hband : ∀ R : ℝ, scales.resolution ≤ R → R ≤ 8*scales.ρ →
      ∀ U : Set P3, MeasurableSet U →
      ∀ center : P3 → ℝ, Measurable center →
      (((d.ν k (p.γ root)).prod volume).restrict S) {z | unshearedPacketBase p root z∈U ∧
        |physicalParentSignal (d.N k) p root (p.R root) z-center (unshearedPacketBase p root z)| ≤ R} ≤
      (ENNReal.ofReal (scales.Cband*R^scales.dimension)*volume U)*
        (ENNReal.ofReal ((hp.frozenPacket root).unitFrame.q)*d.ν k (p.γ root) (p.A root)))
    (level : ℕ) (hlevel : p.lev root ≤ level) (hlast : level ≤ m-1)
    (hend : ∀ z∈S, z∉p.oldEndpoints root ∧ z∉p.levelEndpoints level)
    (hterminal : ∀ z∈S, ∃ terminal : Fin p.C,
      p.lev terminal=m-1 ∧ p.γ terminal=p.γ root ∧ z∈p.F terminal)
    (hT : scales.T=p.T level-p.T (p.lev root)) :
    let pm := model hp root Vmax hVmax source hsource hsourceF
    let ν := d.ν k (p.γ root)
    let E := (hp.frozenPacket root).selectedEvent S
    let μ := ((pm.prior ν).prod volume).restrict E
    let code := clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) scales.b
    let nativeRow := row ∘ (code ∘ p.childClockPoint root)
    let lab := p.childClockLabel root level (p.γ root)
    letI : IsProbabilityMeasure ν := (hd.weights k).2.2 _
    letI : IsProbabilityMeasure (pm.prior ν) := model_prior_probability hp root hVmax source hsource hsourceF hd
    letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
      (Parent.Graph.prod_unit_finite (pm.prior ν) (fun z hz => ⟨mem_univ _,pm.event_time z (image_mono hSsource hz)⟩)).ne
    RootPreparationSupply pm ν μ E row nativeRow lab scales := by
  let pm := model hp root Vmax hVmax source hsource hsourceF
  let packet := hp.frozenPacket root
  let ν := d.ν k (p.γ root)
  let Eclock := packet.selectedEvent S
  let μ := ((pm.prior ν).prod volume).restrict Eclock
  let code := clockParentCode p root (Parent.SignalGraph.ancestorSignal (d.N k) p root) scales.b
  let nativeRow := row ∘ (code ∘ p.childClockPoint root)
  let lab := p.childClockLabel root level (p.γ root)
  letI : IsProbabilityMeasure ν := (hd.weights k).2.2 _
  letI : IsProbabilityMeasure (pm.prior ν) := model_prior_probability hp root hVmax source hsource hsourceF hd
  have hA : ν (p.A root)≠0 := (hp.assignment_mass_pos (by linarith [hd.1 k]) root).ne'
  have hselected : packet.selectedLaw ν S=μ := by
    dsimp only [μ,pm]
    rw [model_prior]
    rfl
  have hEclock : MeasurableSet Eclock := packet.measurable_selectedEvent hS
  have hEp : Eclock⊆pm.event := image_mono hSsource
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (Parent.Graph.prod_unit_finite (pm.prior ν) (fun z hz => ⟨mem_univ _,pm.event_time z (hEp hz)⟩)).ne
  have hcoeff : ∀ l j, |pm.scalarCoefficients l j| ≤ scales.H := fun l j =>
    (model_global_coefficients hp root hVmax source hsource hsourceF l j).trans hcoeffH
  have hstateEq (x : Ev) (hx : x∈S) : pm.physicalState scales.b (packet.timeChange x)=code x :=
    model_physicalState hp root hVmax source hsource hsourceF hR hvelocity (hSsource hx) scales.b
  have hG : ∀ z∈Eclock, ∀ j, |row (pm.physicalState scales.b z) j| ≤ scales.B :=
    fun z _ j => hrow _ j
  have hgraph : ∀ z∈Eclock, |(pm.signal z.1).derivative.eval z.2-
      ∑ j, row (pm.physicalState scales.b z) j*pm.velocity z.1 j| ≤ scales.error := by
    rintro z ⟨x,hx,rfl⟩
    rw [hstateEq x hx,model_rate hp root hVmax source hsource hsourceF hR hvelocity (hSsource hx)]
    have hv : pm.velocity (packet.timeChange x).1=(![1,Parent.v x.1 0,Parent.v x.1 1] : Fin 3 → ℝ) := by
      rw [Parent.Graph.clock_timeChange hp root x]
      have hv' := model_velocity hp root hVmax source hsource hsourceF hR hvelocity (hSsource hx)
      funext j
      fin_cases j
      · rfl
      · exact congrFun hv' 0
      · exact congrFun hv' 1
    rw [hv]
    exact hfit x hx
  have hfloors : Jets2.OriginalDyadicFloorData (pm.prior ν) pm.scalarCoefficients Eclock palette
      scales.dimension scales.floorExponent scales.floorStart scales.floorCount := by
    simpa only [pm,model_prior,model_coefficientTable] using floors
  have htables : Jets2.OriginalDerivativeListData pm.scalarCoefficients Eclock
      (fun i : Fin scales.regLength => scales.regLevel i.val) (fun _ => scales.KL) := by
    simpa only [pm,model_coefficientTable] using tables
  have hvelocityClock : ∀ᵐ z ∂μ, ‖pm.planarVelocityVector z.1‖ ≤ scales.Uvelocity := by
    filter_upwards [ae_restrict_mem hEclock] with z hz
    obtain ⟨x,hx,rfl⟩ := hz
    rw [Parent.Graph.clock_timeChange hp root x,
      model_planarVelocityVector hp root hVmax source hsource hsourceF hR hvelocity (hSsource hx)]
    exact (hvelocity x (hSsource hx)).trans hVmaxU
  have hstripClock : ∀ q (normal : EuclideanSpace ℝ (Fin 2)) offset, ‖normal‖=1 →
      μ {z | pm.physicalState scales.b z=q ∧
        |inner ℝ normal (pm.planarVelocityVector z.1)-offset| ≤ scales.stripWidth} ≤
      ENNReal.ofReal scales.failure*μ ((pm.physicalState scales.b) ⁻¹' {q}) := by
    intro q normal offset hnormal
    have hh := model_state_strip_cap hp root hVmax source hsource hsourceF hR hvelocity ν hA
      S hS hSsource scales.b q normal offset scales.stripWidth stripCoeff
      (ratios.2.1 q normal offset hnormal)
    rw [hselected] at hh
    exact hh.trans (mul_le_mul' hstripCoeff le_rfl)
  have hstateClock : ∀ query : ℕ, query ≤ scales.paletteFinest →
      ∀ q (D : Set (Fin 2 → ℤ)), MeasurableSet D →
      μ {z | pm.physicalState scales.b z=q ∧
        Jets2.parameterCode (Jets2.dyadicParameterWidth query) (Jets2.zv (pm.scalarCoefficients z.1))∈D} ≤
      ENNReal.ofReal scales.incidence.Cstate*μ ((pm.physicalState scales.b) ⁻¹' {q})*
        (palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth query))) D := by
    intro query hquery q D hD
    have hh := model_current_velocity_ratio hp root hVmax source hsource hsourceF hR hvelocity ν hA
      S hS hSsource scales.b (Jets2.dyadicParameterWidth query) q D hD
      (palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth query))) (4*paletteCoeff)
      (ratios.dyadic_current_caps reference hfinePv hfineWidth query hquery q D hD)
    rw [hselected] at hh
    exact hh.trans (mul_le_mul' (mul_le_mul' hpaletteCoeff le_rfl) le_rfl)
  have hpureClock : ∀ query : ℕ, query ≤ scales.paletteFinest →
      ∀ w : ℝ, scales.resolution ≤ w → w ≤ 1 → ∀ base hidden vcode,
      μ {z | Jets2.originalBaseCode pm.scalarCoefficients scales.resolution z=base ∧
        ⌊Jets2.zx (pm.scalarCoefficients z.1) z.2/w⌋=hidden ∧
        Jets2.parameterCode (Jets2.dyadicParameterWidth query) (Jets2.zv (pm.scalarCoefficients z.1))=vcode} ≤
      ENNReal.ofReal (scales.Cpure*scales.resolution^3*w^scales.dimension)*
        (palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth query))) {vcode} := by
    intro query hquery w hw hw1 base hidden vcode
    have hh := model_scalar_pure_cap hp root hVmax source hsource hsourceF hR hvelocity ν hA
      S hS hSsource scales.resolution w (Jets2.dyadicParameterWidth query) base hidden {vcode}
      (measurableSet_singleton _) _ (hpure query hquery w hw hw1 base hidden {vcode} (measurableSet_singleton _))
    rw [hselected] at hh
    exact hh
  have hcensusClock : ∀ a w : ℝ, scales.resolution ≤ a → a ≤ 1 → scales.resolution ≤ w → w ≤ 1 →
      scales.Kcensus^(100:ℕ)*a ≤ w →
      (occupied Eclock (fun z j => pm.originalBase z j) (fun z => pm.originalPoint z 3) a w).Finite ∧
      ((occupied Eclock (fun z j => pm.originalBase z j) (fun z => pm.originalPoint z 3) a w).ncard:ℝ) ≤
        scales.Kcensus/(a^3*w^scales.dimension) := by
    intro a w ha ha1 hw hw1 hshape
    have hh := model_occupied hp root hVmax source hsource hsourceF hR hvelocity S hSsource a w 1
    simp only [div_one] at hh
    rw [hh]
    exact hcensus a w ha ha1 hw hw1 hshape
  have hbandClock : ∀ R : ℝ, scales.resolution ≤ R → R ≤ 8*scales.ρ →
      ∀ U : Set P3, MeasurableSet U →
      ∀ center : P3 → ℝ, Measurable center →
      μ {z | pm.originalBase z∈U ∧ |pm.originalPoint z 3-center (pm.originalBase z)| ≤ R} ≤
      ENNReal.ofReal (scales.Cband*R^scales.dimension)*volume U := by
    intro R hRlo hRhi U hU center hcenter
    have hh := model_moving_band_cap hp root hVmax source hsource hsourceF hR hvelocity ν hA S hS hSsource
      U hU center hcenter R _ (hband R hRlo hRhi U hU center hcenter)
    rwa [hselected] at hh
  have hnativeMeas : Measurable nativeRow :=
    (measurable_of_countable row).comp ((measurable_clockParentCode p root _ scales.b).comp
      (p.childClockPoint_measurable root))
  have hpoint (z : Ev) : p.childClockPoint root z=packet.timeChange.symm z :=
    congrFun (hp.childClockPoint_eq_timeChange_symm root) z
  have hreadout : ∀ z∈Eclock, nativeRow z=row (pm.physicalState scales.b z) := by
    rintro z ⟨x,hx,rfl⟩
    dsimp only [nativeRow,Function.comp_apply]
    rw [hpoint,MeasurableEquiv.symm_apply_apply,hstateEq x hx]
  have hreference : Eclock⊆p.childClockReference root level S := by
    rintro z ⟨x,hx,rfl⟩
    change p.childClockPoint root (packet.timeChange x)∈p.childReference root level S
    rw [hpoint,MeasurableEquiv.symm_apply_apply]
    exact ⟨⟨hx,(hend x hx).1⟩,(hend x hx).2⟩
  have hlabel : ∀ z∈Eclock, ∀ v, (z.1,v)∈Eclock → v∈Jets2.dyadicBlock scales.T z.2 → lab (z.1,v)=lab z := by
    intro z hz v hv hb
    rw [hT] at hb
    exact hp.childClockLabel_same_block root level hlevel hlast S (hSsource.trans hsourceF) hterminal
      z (hreference hz) v (hreference hv) hb
  exact rootPreparationSupply_of_original_data pm ν scales
    (model_slack_one_le hp root hVmax source hsource hsourceF) Eclock hEclock hEp hcoeff row hG hgraph
    palette hfloors htables hvelocityClock hstripClock hstateClock hpureClock hcensusClock hbandClock
    nativeRow hnativeMeas hreadout lab (hp.childClockLabel_measurable root level _) (to_countable _).measurableSet hlabel

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
