-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.OriginalRootFromData, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalRootInput
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalIncidenceFromPureCells
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DerivativeListsFromDyadicFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CurrentPaletteRealDomination

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

/-- Numerical choices for root preparation. The structure has no
coefficient table, source, prior, row or analytic certificate. -/
structure OriginalRootScales where
  b : ℝ
  ρ : ℝ
  H : ℝ
  B : ℝ
  error : ℝ
  Lp : ℝ
  Uvelocity : ℝ
  stripWidth : ℝ
  radius : ℝ
  failure : ℝ
  hb : 0 < b
  hρ : 0 < ρ
  hρ1 : ρ ≤ 1
  hbρ : b ≤ ρ
  hH : 1 ≤ H
  hB : 1 ≤ B
  hHB : H ≤ B
  he : 0 ≤ error
  hLp : 0 ≤ Lp
  hUvelocity : 0 ≤ Uvelocity
  hfailure : 0 ≤ failure
  hfailure1 : failure < 1
  regLength : ℕ
  hregLength : 1 ≤ regLength
  regLevel : ℕ → ℕ
  hreg0 : regLevel 0=0
  regSteps : ℕ → ℕ
  hregEq : ∀ i < regLength, Jets2.dyadicParameterWidth (regLevel i)=b*(2:ℝ)^(regSteps i)
  hbreg : ∀ i < regLength, b ≤ Jets2.dyadicParameterWidth (regLevel i)
  Ar : ℝ
  hAr : 1 ≤ Ar
  hregRatio : ∀ i, i+1 < regLength → Jets2.dyadicParameterWidth (regLevel i) ≤
    Ar*Jets2.dyadicParameterWidth (regLevel (i+1))
  hregFloor : Jets2.dyadicParameterWidth (regLevel (regLength-1)) ≤ ρ
  rhoBroad : ℝ
  D : ℝ
  KL : ℝ
  Areg : ℝ
  hBroadRadius : 0 < rhoBroad
  hBroadSmall : rhoBroad ≤ 1/4
  hBroadWidth : 2*(Uvelocity+1)*rhoBroad ≤ stripWidth
  hD : 0 < D
  hAreg : 1 ≤ Areg
  hBA : B ≤ Areg
  hKLA : KL ≤ Areg
  hDA : D ≤ Areg
  hcA : (1-failure)⁻¹ ≤ Areg
  hρA : rhoBroad⁻¹ ≤ Areg
  heA : ∀ i < regLength, error/Jets2.dyadicParameterWidth (regLevel i) ≤ Areg
  hLpReg : 6*(Ar+3*B) ≤ Lp
  W : Finset ℝ
  resolution : ℝ
  Kcensus : ℝ
  dimension : ℝ
  Cband : ℝ
  rate : ℝ
  Hprior : ℝ
  hresolution : 0 < resolution
  hKcensus : 1 ≤ Kcensus
  hCband : 0 ≤ Cband
  hrate : 0 < rate
  hHprior : 0 < Hprior
  steps : ℕ
  hsteps : Kcensus^(100:ℕ) ≤ (2:ℝ)^steps
  hb_eq : b=resolution*(2:ℝ)^steps
  fineSteps : ℝ → ℕ
  columnSteps : ℝ → ℕ
  hwidth : ∀ w∈W, w=b*(2:ℝ)^(fineSteps w)
  hcolumn : ∀ w∈W, ρ=w*(2:ℝ)^(columnSteps w)
  hbw : ∀ w∈W, b ≤ w
  hwρ : ∀ w∈W, w ≤ ρ
  hround : ∀ w∈W, (1+3*B)*b ≤ w
  hgraphWidth : ∀ w∈W, error*ρ ≤ w
  hrowWidth : ∀ w∈W, Lp*H*ρ^2 ≤ w
  Cmk : ℝ
  Kfill : ℝ
  hradius : 0 < radius
  hCmk : 0 ≤ Cmk
  hMK : FiniteMK 3 Cmk
  hKfill : 0 < Kfill
  hdim : 0 ≤ dimension
  hdim1 : dimension ≤ 1
  hfillBudget : (8*Cmk*7^3)^2*(3*Hprior)^3 ≤ ((radius/2)^3/2*(1-failure)^3)*Kfill
  hPencilWidth : 2*(Uvelocity+1)*((Uvelocity+1)*radius) ≤ stripWidth
  hPencilSmall : (Uvelocity+1)*radius ≤ 1/4
  zeta : ℝ
  hzeta : 0 < zeta
  hzeta1 : zeta ≤ 1
  hworldSmall : ∀ w∈W, 4*(2*((3*H+1)*Lp)*ρ+4*Lp*ρ)*ρ+(1+3*B)*b ≤ w/2
  hworldScales : ∀ r : ℝ, zeta ≤ r → r ≤ 1 → ∃ w∈W, w ≤ ρ*r ∧ ρ*r ≤ 2*w
  Krow : ℝ
  eta : ℝ
  Htarget : ℝ
  Kcap : ℝ
  Cpure : ℝ
  hCpure : 0 ≤ Cpure
  hKcap : 0 < Kcap
  hBKrow : B ≤ Krow
  hRCKrow : 3*((3*H+1)*Lp) ≤ Krow
  hFitEta : 2*((3*H+1)*Lp)*ρ ≤ eta
  hrowTarget : Krow ≤ Htarget
  floorStart : ℕ
  floorCount : ℕ
  floorExponent : ℝ
  incidence : Jets2.OriginalIncidenceScales b ρ H Krow eta error zeta dimension
    (worldScalarSupportConstant B Cband rate Kfill 2) Htarget Kcap Cpure floorStart floorCount floorExponent
  hincResolution : incidence.resolution=resolution
  paletteFinest : ℕ
  hincFinest : incidence.n0+incidence.lastLevel ≤ paletteFinest
  hregFinest : ∀ i < regLength, regLevel i ≤ paletteFinest
  hstateD : incidence.Cstate ≤ D
  T : ℕ
  hTlo : incidence.N^(-incidence.ch)/(incidence.N^(incidence.ch*incidence.alpha)) ≤ ((2:ℝ)^T)⁻¹
  hThi : ((2:ℝ)^T)⁻¹ ≤ (incidence.N^(incidence.ch*incidence.alpha))*incidence.N^(-incidence.ch)
  hζT : zeta ≤ ((2:ℝ)^T)⁻¹^incidence.cZeta
  mesh : ℝ
  err : ℝ
  duration : ℝ
  bound : ℤ
  hmesh : 0 < mesh
  hbound : 3*H+(1+2*H)*incidence.N^(incidence.ch*incidence.analyticEpsilon) ≤ mesh*(bound-1)
  herror : error+(1+2*H)*(eta+((2:ℝ)^T)⁻¹^((incidence.M:ℝ)+1/8))+(incidence.M+1)*mesh ≤ err
  hduration : duration ≤ ((2:ℝ)^T)⁻¹*incidence.N^(-(incidence.ch*incidence.analyticEpsilon))

/-- Actual P1 floors/tables and P5 same-current strips/palettes fill
the root input. Canonical caps, velocity carriers, real state ratios
and every incidence floor are derived internally. -/
def rootPreparationInput_of_original_data (p : PhysicalModel) (ν : Measure Ln)
    [IsProbabilityMeasure (p.prior ν)]
    (scales : OriginalRootScales) (hκ : 1 ≤ p.slack)
    (E : Set Ev) (hE : MeasurableSet E) (hEp : E⊆p.event)
    (hcoeff : ∀ l, ∀ j, |p.scalarCoefficients l j| ≤ scales.H)
    (G : (Fin 4 → ℤ) → Fin 3 → ℝ)
    (hG : ∀ z∈E, ∀ j, |G (p.physicalState scales.b z) j| ≤ scales.B)
    (hgraph : ∀ z∈E, |(p.signal z.1).derivative.eval z.2-
      ∑ j, G (p.physicalState scales.b z) j*p.velocity z.1 j| ≤ scales.error)
    (palette : Measure (Fin 2 → ℝ))
    (floors : Jets2.OriginalDyadicFloorData (p.prior ν) p.scalarCoefficients E palette scales.dimension
      scales.floorExponent scales.floorStart scales.floorCount)
    (tables : Jets2.OriginalDerivativeListData p.scalarCoefficients E
      (fun i : Fin scales.regLength => scales.regLevel i.val) (fun _ => scales.KL))
    (hvelocity : ∀ᵐ z ∂((p.prior ν).prod volume).restrict E, ‖p.planarVelocityVector z.1‖ ≤ scales.Uvelocity)
    (hstrip : ∀ q (normal : EuclideanSpace ℝ (Fin 2)) offset, ‖normal‖=1 →
      (((p.prior ν).prod volume).restrict E) {z | p.physicalState scales.b z=q ∧
        |inner ℝ normal (p.planarVelocityVector z.1)-offset| ≤ scales.stripWidth} ≤
      ENNReal.ofReal scales.failure*(((p.prior ν).prod volume).restrict E)
        ((p.physicalState scales.b) ⁻¹' {q}))
    (hstate : ∀ query : ℕ, query ≤ scales.paletteFinest → ∀ q (D : Set (Fin 2 → ℤ)), MeasurableSet D →
      (((p.prior ν).prod volume).restrict E) {z | p.physicalState scales.b z=q ∧
        Jets2.parameterCode (Jets2.dyadicParameterWidth query) (Jets2.zv (p.scalarCoefficients z.1))∈D} ≤
      ENNReal.ofReal scales.incidence.Cstate*(((p.prior ν).prod volume).restrict E)
        ((p.physicalState scales.b) ⁻¹' {q})*
          (palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth query))) D)
    (hpure : ∀ query : ℕ, query ≤ scales.paletteFinest → ∀ w : ℝ, scales.resolution ≤ w → w ≤ 1 →
      ∀ (base : Fin 3 → ℤ) (hidden : ℤ) (vcode : Fin 2 → ℤ),
      (((p.prior ν).prod volume).restrict E) {z | Jets2.originalBaseCode p.scalarCoefficients scales.resolution z=base ∧
        ⌊Jets2.zx (p.scalarCoefficients z.1) z.2/w⌋=hidden ∧
        Jets2.parameterCode (Jets2.dyadicParameterWidth query) (Jets2.zv (p.scalarCoefficients z.1))=vcode} ≤
      ENNReal.ofReal (scales.Cpure*scales.resolution^3*w^scales.dimension)*
        (palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth query))) {vcode})
    (hcensus : ∀ a w : ℝ, scales.resolution ≤ a → a ≤ 1 → scales.resolution ≤ w → w ≤ 1 →
      scales.Kcensus^(100:ℕ)*a ≤ w →
      (occupied E (fun z j => p.originalBase z j) (fun z => p.originalPoint z 3) a w).Finite ∧
      ((occupied E (fun z j => p.originalBase z j) (fun z => p.originalPoint z 3) a w).ncard:ℝ) ≤
        scales.Kcensus/(a^3*w^scales.dimension))
    (hband : ∀ R : ℝ, scales.resolution ≤ R → R ≤ 8*scales.ρ →
      ∀ U : Set P3, MeasurableSet U → ∀ center : P3 → ℝ, Measurable center →
      (((p.prior ν).prod volume).restrict E)
        {z | p.originalBase z∈U ∧ |p.originalPoint z 3-center (p.originalBase z)| ≤ R} ≤
        ENNReal.ofReal (scales.Cband*R^scales.dimension)*volume U)
    (nativeRow : Ev → Fin 3 → ℝ) (hNativeRow : Measurable nativeRow)
    (hNativeRowEq : ∀ z∈E, nativeRow z=G (p.physicalState scales.b z))
    {Label : Type} [MeasurableSpace Label] (lab : Ev → Label) (hlab : Measurable lab)
    (hdiag : MeasurableSet {q : Label × Label | q.1=q.2})
    (hlabel : ∀ z∈E, ∀ v, (z.1,v)∈E → v∈Jets2.dyadicBlock scales.T z.2 → lab (z.1,v)=lab z) :
    let μ := (((p.prior ν).prod volume).restrict E)
    letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
      (Graph.prod_unit_finite (p.prior ν) (fun z hz => ⟨mem_univ _,p.event_time z (hEp hz)⟩)).ne
    RootPreparationInput p ν μ E G nativeRow lab := by
  let μ := (((p.prior ν).prod volume).restrict E)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (Graph.prod_unit_finite (p.prior ν) (fun z hz => ⟨mem_univ _,p.event_time z (hEp hz)⟩)).ne
  have hμE : μ.restrict E=μ := by rw [Measure.restrict_restrict hE,inter_self]
  have hfull : ∀ᵐ z ∂μ, z∈E := ae_restrict_mem hE
  letI : IsProbabilityMeasure palette := floors.probability
  have hprob (query : ℕ) : IsProbabilityMeasure (palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth query))) :=
    (Measure.isProbabilityMeasure_map_iff (Jets2.measurable_parameterCode _).aemeasurable).mpr inferInstance
  letI : ∀ query, IsProbabilityMeasure (palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth query))) := hprob
  have hphysical (s : ℝ) (z : Ev) : cell s (Graph.physX p z)=p.physicalState s z := rfl
  have hfine (z : Ev) (q : Fin 4 → ℤ) :
      Jets2.originalFineState p.scalarCoefficients scales.b z=q ↔
        p.physicalState scales.b z=scalarStateToPhysical q := by
    rw [p.physicalState_eq_scalarState]
    exact scalarStateToPhysical_injective.eq_iff.symm
  have hstateScalar (query : ℕ) (hq : query ≤ scales.incidence.n0+scales.incidence.lastLevel)
      (q : Fin 4 → ℤ) (D : Set (Fin 2 → ℤ)) (hD : MeasurableSet D) :=
    hstate query (hq.trans scales.hincFinest) (scalarStateToPhysical q) D hD
  have hstateScalar' : ∀ query : ℕ, query ≤ scales.incidence.n0+scales.incidence.lastLevel →
      ∀ q (D : Set (Fin 2 → ℤ)), MeasurableSet D →
      μ {z | Jets2.originalFineState p.scalarCoefficients scales.b z=q ∧
        Jets2.parameterCode (Jets2.dyadicParameterWidth query) (Jets2.zv (p.scalarCoefficients z.1))∈D} ≤
      ENNReal.ofReal scales.incidence.Cstate*μ ((Jets2.originalFineState p.scalarCoefficients scales.b) ⁻¹' {q})*
        (palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth query))) D := by
    intro query hq q D hD
    rw [p.original_scalar_state_fiber]
    simp_rw [hfine]
    exact hstateScalar query hq q D hD
  have hpure' : ∀ query : ℕ, query ≤ scales.incidence.n0+scales.incidence.lastLevel →
      ∀ w : ℝ, scales.incidence.resolution ≤ w → w ≤ 1 →
      ∀ (base : Fin 3 → ℤ) (hidden : ℤ) (vcode : Fin 2 → ℤ),
      (μ.restrict E) {z | Jets2.originalBaseCode p.scalarCoefficients scales.incidence.resolution z=base ∧
        ⌊Jets2.zx (p.scalarCoefficients z.1) z.2/w⌋=hidden ∧
        Jets2.parameterCode (Jets2.dyadicParameterWidth query) (Jets2.zv (p.scalarCoefficients z.1))=vcode} ≤
      ENNReal.ofReal (scales.Cpure*scales.incidence.resolution^3*w^scales.dimension)*
        (palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth query))) {vcode} := by
    simpa only [scales.hincResolution,hμE] using
      (fun query hq => hpure query (hq.trans scales.hincFinest))
  let incidence := Jets2.originalIncidenceData_of_pure_cells (p.prior ν) μ p.scalarCoefficients
    p.measurable_scalarCoefficients E hE scales.incidence palette floors scales.hρ scales.hρ1 scales.hH
    scales.hKcap scales.hCpure scales.hdim (fun z hz => p.event_time z (hEp hz))
    (fun z _ j => hcoeff z.1 j) rfl hpure' hstateScalar'
  have hfinite (i : ℕ) : ((fun z : Ev => vbin (Jets2.dyadicParameterWidth (scales.regLevel i))
      (Graph.planarVel p z.1)) '' E).Finite := by
    have hh := Submission.Lib.K4ContinuousPlanks.finite_range_floor_code
      (fun z : E => Graph.planarVel p z.val.1) scales.H (fun z j => by
        fin_cases j
        · exact hcoeff z.val.1 4
        · exact hcoeff z.val.1 6) (Jets2.dyadicParameterWidth_pos (scales.regLevel i))
    apply hh.subset
    rintro q ⟨z,hz,rfl⟩
    exact ⟨⟨z,hz⟩,rfl⟩
  let velocityBins := fun i => (hfinite i).toFinset
  let weight := fun i v => ((palette.map (Jets2.parameterCode
    (Jets2.dyadicParameterWidth (scales.regLevel i)))) {v}).toReal
  let lists := fun i q v => if hi : i < scales.regLength then
    tables.lists ⟨i,hi⟩ (physicalStateToScalar q) v else ∅
  have hstateDom (i : ℕ) (hi : i < scales.regLength) :=
    real_state_domination_of_current_caps μ E hfull (p.physicalState scales.b)
      (fun z => vbin (Jets2.dyadicParameterWidth (scales.regLevel i)) (Graph.planarVel p z.1))
      (palette.map (Jets2.parameterCode (Jets2.dyadicParameterWidth (scales.regLevel i))))
      scales.incidence.hCstate (fun q v => hstate (scales.regLevel i) (scales.hregFinest i hi) q {v}
        (measurableSet_singleton _))
  refine {
    hκ := hκ, Kden := 1, hKden := by norm_num, hE := hE, hEp := hEp,
    hfull := hfull, hdom := by simpa only [one_smul] using (Measure.restrict_le_self : μ ≤ _),
    b := scales.b, ρ := scales.ρ, H := scales.H, B := scales.B, error := scales.error, Lp := scales.Lp,
    Uvelocity := scales.Uvelocity, stripWidth := scales.stripWidth, radius := scales.radius, failure := scales.failure,
    hb := scales.hb, hρ := scales.hρ, hρ1 := scales.hρ1, hbρ := scales.hbρ,
    hH := scales.hH, hB := scales.hB, he := scales.he, hLp := scales.hLp,
    hjets := fun l _ => ⟨hcoeff l 1,hcoeff l 2,hcoeff l 4,hcoeff l 6⟩, hG := hG,
    hvel := ?_, hgraph := hgraph, hUvelocity := scales.hUvelocity, hfailure := scales.hfailure,
    hfailure1 := scales.hfailure1, hvelocity := hvelocity, hstrip := hstrip,
    regLength := scales.regLength, hregLength := scales.hregLength,
    regScale := fun i => Jets2.dyadicParameterWidth (scales.regLevel i),
    hreg0 := by rw [scales.hreg0]; norm_num [Jets2.dyadicParameterWidth],
    hregPos := fun _ => Jets2.dyadicParameterWidth_pos _, hbreg := scales.hbreg,
    Ar := scales.Ar, hAr := scales.hAr, hregRatio := scales.hregRatio, hregFloor := scales.hregFloor,
    hregNest := ?_, regWeight := weight, velocityBins := velocityBins, derivativeLists := lists,
    rhoBroad := scales.rhoBroad, D := scales.D, KL := scales.KL, Areg := scales.Areg, P := 1,
    hBroadRadius := scales.hBroadRadius, hBroadSmall := scales.hBroadSmall, hBroadWidth := scales.hBroadWidth,
    hD := scales.hD, hAreg := scales.hAreg, hBA := scales.hBA, hKLA := scales.hKLA,
    hDA := scales.hDA, hcA := scales.hcA, hρA := scales.hρA, heA := scales.heA,
    hweight := fun _ _ => ENNReal.toReal_nonneg, hP := ?_, hderiv := ?_, hderivCard := ?_,
    hvelocityBins := ?_, hstateDom := ?_, hLpReg := scales.hLpReg,
    W := scales.W, resolution := scales.resolution, Kcensus := scales.Kcensus, dimension := scales.dimension,
    Cband := scales.Cband, rate := scales.rate, Hprior := scales.Hprior,
    hresolution := scales.hresolution, hKcensus := scales.hKcensus, hCband := scales.hCband,
    hrate := scales.hrate, hHprior := scales.hHprior, steps := scales.steps, hsteps := scales.hsteps,
    hb_eq := scales.hb_eq, fineSteps := scales.fineSteps, columnSteps := scales.columnSteps,
    hwidth := scales.hwidth, hcolumn := scales.hcolumn, hbw := scales.hbw, hwρ := scales.hwρ,
    hround := scales.hround, hgraphWidth := scales.hgraphWidth, hrowWidth := scales.hrowWidth,
    hcensus := hcensus, hband := hband, Cmk := scales.Cmk, Kfill := scales.Kfill,
    hradius := scales.hradius, hCmk := scales.hCmk, hMK := scales.hMK, hKfill := scales.hKfill,
    hdim := scales.hdim, hdim1 := scales.hdim1,
    hfillBudget := by simpa only [NNReal.coe_one,mul_one] using scales.hfillBudget,
    hPencilWidth := scales.hPencilWidth, hPencilSmall := scales.hPencilSmall,
    zeta := scales.zeta, Lambda := 2, hzeta := scales.hzeta, hzeta1 := scales.hzeta1,
    hLambda := by norm_num, hworldSmall := scales.hworldSmall, hworldScales := scales.hworldScales,
    hμ := rfl, hcoeff := fun l _ j => hcoeff l j, Krow := scales.Krow, eta := scales.eta,
    Htarget := scales.Htarget, Kcap := scales.Kcap, profileAmplitude := 1,
    hBKrow := scales.hBKrow, hRCKrow := scales.hRCKrow, hFitEta := scales.hFitEta,
    hrowTarget := scales.hrowTarget, paletteRef := palette, incidence := incidence,
    hNativeRow := hNativeRow, hNativeRowEq := hNativeRowEq,
    T := scales.T, hTlo := scales.hTlo, hThi := scales.hThi, hζT := scales.hζT,
    hlab := hlab, hdiag := hdiag, hlabel := hlabel,
    mesh := scales.mesh, err := scales.err, duration := scales.duration, bound := scales.bound,
    hmesh := scales.hmesh, hbound := scales.hbound, herror := scales.herror, hduration := scales.hduration }
  · intro z hz j
    fin_cases j
    · exact (hcoeff z.1 4).trans scales.hHB
    · exact (hcoeff z.1 6).trans scales.hHB
  · intro i hi x hx z hz hstate
    exact Graph.cell_eq_of_physicalState_eq p (scales.regSteps i) (scales.hregEq i hi) hstate
  · intro i hi
    letI := hprob (scales.regLevel i)
    exact probability_palette_sum_le_one _ _
  · intro i hi z hz
    dsimp only [lists]
    rw [dite_eq_left hi,hphysical,←p.scalarState_eq_physicalState]
    exact tables.known ⟨i,hi⟩ z hz
  · intro i hi q v
    dsimp only [lists]
    rw [dite_eq_left hi]
    exact tables.card ⟨i,hi⟩ _ _
  · intro i hi z hz
    exact (hfinite i).mem_toFinset.mpr ⟨z,hz,rfl⟩
  · intro i hi z hz v
    have hh := hstateDom i hi z hz v
    exact hh.trans (by
      apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
      exact mul_le_mul_of_nonneg_right scales.hstateD measureReal_nonneg)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
