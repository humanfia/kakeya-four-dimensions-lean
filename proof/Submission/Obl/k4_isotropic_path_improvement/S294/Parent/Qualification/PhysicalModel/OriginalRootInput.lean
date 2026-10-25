-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.OriginalRootInput, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.OriginalRootPreparation

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

/-- The primitive input data of original root preparation: numerical
scales, current incidence caps, original coefficient floors and the
actual row/derivative table. The scalar supports, residual comparison
and native failure bounds are constructed by `run`. -/
structure RootPreparationInput (p : PhysicalModel) (ν : Measure Ln)
    [IsProbabilityMeasure (p.prior ν)] (μ : Measure Ev) [IsFiniteMeasure μ]
    (E : Set Ev) (G : (Fin 4 → ℤ) → Fin 3 → ℝ)
    (nativeRow : Ev → Fin 3 → ℝ) {Label : Type} [MeasurableSpace Label] (lab : Ev → Label) where
  hκ : 1 ≤ p.slack
  Kden : NNReal
  hKden : 0 < Kden
  hE : MeasurableSet E
  hEp : E ⊆ p.event
  hfull : ∀ᵐ z ∂μ, z∈E
  hdom : μ ≤ Kden • (p.prior ν).prod volume
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
  he : 0 ≤ error
  hLp : 0 ≤ Lp
  hjets : ∀ l∈p.assigned, |p.scalarCoefficients l 1| ≤ H ∧
        |p.scalarCoefficients l 2| ≤ H ∧ |p.scalarCoefficients l 4| ≤ H ∧
          |p.scalarCoefficients l 6| ≤ H
  hG : ∀ z∈E, ∀ j, |G (p.physicalState b z) j| ≤ B
  hvel : ∀ z∈E, ∀ j, |Graph.planarVel p z.1 j| ≤ B
  hgraph : ∀ z∈E, |(p.signal z.1).derivative.eval z.2-
        ∑ j, G (p.physicalState b z) j*p.velocity z.1 j| ≤ error
  hUvelocity : 0 ≤ Uvelocity
  hfailure : 0 ≤ failure
  hfailure1 : failure < 1
  hvelocity : ∀ᵐ z ∂μ, ‖p.planarVelocityVector z.1‖ ≤ Uvelocity
  hstrip : ∀ q (normal : EuclideanSpace ℝ (Fin 2)) offset, ‖normal‖=1 →
        μ {z | p.physicalState b z=q ∧
          |inner ℝ normal (p.planarVelocityVector z.1)-offset| ≤ stripWidth} ≤
            ENNReal.ofReal failure*μ ((p.physicalState b) ⁻¹' {q})
  regLength : ℕ
  hregLength : 1 ≤ regLength
  regScale : ℕ → ℝ
  hreg0 : regScale 0=1
  hregPos : ∀ i, 0 < regScale i
  hbreg : ∀ i < regLength, b ≤ regScale i
  Ar : ℝ
  hAr : 1 ≤ Ar
  hregRatio : ∀ i, i+1 < regLength → regScale i ≤ Ar*regScale (i+1)
  hregFloor : regScale (regLength-1) ≤ ρ
  hregNest : ∀ i < regLength, ∀ x∈E, ∀ z∈E,
        p.physicalState b x=p.physicalState b z →
          cell (regScale i) (Graph.physX p x)=cell (regScale i) (Graph.physX p z)
  regWeight : ℕ → (Fin 2 → ℤ) → ℝ
  velocityBins : ℕ → Finset (Fin 2 → ℤ)
  derivativeLists : ℕ → (Fin 4 → ℤ) → (Fin 2 → ℤ) → Finset ℤ
  rhoBroad : ℝ
  D : ℝ
  KL : ℝ
  Areg : ℝ
  P : ℝ
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
  heA : ∀ i < regLength, error/regScale i ≤ Areg
  hweight : ∀ i v, 0 ≤ regWeight i v
  hP : ∀ i < regLength, ∑ v∈velocityBins i, regWeight i v ≤ P
  hderiv : ∀ i < regLength, ∀ z∈E,
        ⌊Graph.physRate p z/regScale i⌋∈derivativeLists i
          (cell (regScale i) (Graph.physX p z)) (vbin (regScale i) (Graph.planarVel p z.1))
  hderivCard : ∀ i < regLength, ∀ q v, ((derivativeLists i q v).card:ℝ) ≤ KL
  hvelocityBins : ∀ i < regLength, ∀ z∈E,
        vbin (regScale i) (Graph.planarVel p z.1)∈velocityBins i
  hstateDom : ∀ i < regLength, ∀ z∈E, ∀ v,
        μ.real (E∩(p.physicalState b) ⁻¹' {p.physicalState b z}∩
          {x | vbin (regScale i) (Graph.planarVel p x.1)=v}) ≤
            D*μ.real (E∩(p.physicalState b) ⁻¹' {p.physicalState b z})*regWeight i v
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
  hcensus : ∀ a w : ℝ, resolution ≤ a → a ≤ 1 → resolution ≤ w → w ≤ 1 →
        Kcensus^(100:ℕ)*a ≤ w →
          (occupied E (fun z j => p.originalBase z j) (fun z => p.originalPoint z 3) a w).Finite ∧
          ((occupied E (fun z j => p.originalBase z j) (fun z => p.originalPoint z 3) a w).ncard:ℝ) ≤
            Kcensus/(a^3*w^dimension)
  hband : ∀ R : ℝ, resolution ≤ R → R ≤ 8*ρ →
        ∀ U : Set P3, MeasurableSet U → ∀ center : P3 → ℝ, Measurable center →
        μ {z | p.originalBase z∈U ∧ |p.originalPoint z 3-center (p.originalBase z)| ≤ R} ≤
          ENNReal.ofReal (Cband*R^dimension)*volume U
  Cmk : ℝ
  Kfill : ℝ
  hradius : 0 < radius
  hCmk : 0 ≤ Cmk
  hMK : FiniteMK 3 Cmk
  hKfill : 0 < Kfill
  hdim : 0 ≤ dimension
  hdim1 : dimension ≤ 1
  hfillBudget : (8*Cmk*7^3)^2*(3*(Kden:ℝ)*Hprior)^3 ≤
        ((radius/2)^3/2*(1-failure)^3)*Kfill
  hPencilWidth : 2*(Uvelocity+1)*((Uvelocity+1)*radius) ≤ stripWidth
  hPencilSmall : (Uvelocity+1)*radius ≤ 1/4
  zeta : ℝ
  Lambda : ℝ
  hzeta : 0 < zeta
  hzeta1 : zeta ≤ 1
  hLambda : 1 ≤ Lambda
  hworldSmall : ∀ w∈W,
        4*(2*((3*H+1)*Lp)*ρ+4*Lp*ρ)*ρ+(1+3*B)*b ≤ w/2
  hworldScales : ∀ r : ℝ, zeta ≤ r → r ≤ 1 → ∃ w∈W, w ≤ ρ*r ∧ ρ*r ≤ Lambda*w
  hμ : μ=((p.prior ν).prod volume).restrict E
  hcoeff : ∀ l∈p.assigned, ∀ j, |p.scalarCoefficients l j| ≤ H
  Krow : ℝ
  eta : ℝ
  Htarget : ℝ
  Kcap : ℝ
  profileAmplitude : ℝ
  hBKrow : B ≤ Krow
  hRCKrow : 3*((3*H+1)*Lp) ≤ Krow
  hFitEta : 2*((3*H+1)*Lp)*ρ ≤ eta
  hrowTarget : Krow ≤ Htarget
  paletteRef : Measure (Fin 2 → ℝ)
  incidence : Jets2.OriginalIncidenceData (p.prior ν) μ p.scalarCoefficients E
        b ρ H Krow eta error zeta dimension (worldScalarSupportConstant B Cband rate Kfill Lambda)
        Htarget Kcap profileAmplitude paletteRef
  hNativeRow : Measurable nativeRow
  hNativeRowEq : ∀ z∈E, nativeRow z=G (p.physicalState b z)
  T : ℕ
  hTlo : incidence.N^(-incidence.ch)/(incidence.N^(incidence.ch*incidence.alpha)) ≤ ((2:ℝ)^T)⁻¹
  hThi : ((2:ℝ)^T)⁻¹ ≤ (incidence.N^(incidence.ch*incidence.alpha))*incidence.N^(-incidence.ch)
  hζT : zeta ≤ ((2:ℝ)^T)⁻¹^incidence.cZeta
  hlab : Measurable lab
  hdiag : MeasurableSet {q : Label × Label | q.1=q.2}
  hlabel : ∀ z∈E, ∀ v, (z.1,v)∈E → v∈Jets2.dyadicBlock T z.2 → lab (z.1,v)=lab z
  mesh : ℝ
  err : ℝ
  duration : ℝ
  bound : ℤ
  hmesh : 0 < mesh
  hbound : 3*H+(1+2*H)*incidence.N^(incidence.ch*incidence.analyticEpsilon) ≤ mesh*(bound-1)
  herror : error+(1+2*H)*(eta+((2:ℝ)^T)⁻¹^((incidence.M:ℝ)+1/8))+(incidence.M+1)*mesh ≤ err
  hduration : duration ≤ ((2:ℝ)^T)⁻¹*incidence.N^(-(incidence.ch*incidence.analyticEpsilon))


section Costs

variable {p : PhysicalModel} {ν : Measure Ln} [IsProbabilityMeasure (p.prior ν)]
    {μ : Measure Ev} [IsFiniteMeasure μ] {E : Set Ev} {G : (Fin 4 → ℤ) → Fin 3 → ℝ}
    {nativeRow : Ev → Fin 3 → ℝ} {Label : Type} [MeasurableSpace Label] {lab : Ev → Label}
    (input : RootPreparationInput p ν μ E G nativeRow lab)

def RootPreparationInput.regularityFactor : ENNReal :=
  ∏ i∈Finset.range input.regLength,
    ((4:ENNReal)^4*((7:ℕ)^4*⌊10^10*input.Areg^27*(input.P^3+1)⌋₊))

def RootPreparationInput.supportLoss : ENNReal :=
  ENNReal.ofReal ((300*7^8*input.H)*(input.W.card:ℝ)/input.Hprior)+
    ENNReal.ofReal ((input.Kcensus*((2:ℝ)^input.steps)^3)*((input.W.card:ℝ)*input.rate))

end Costs

/-- Run the constructive root producer, forming its witness reference
only after its final whole-state source has been selected. -/
theorem RootPreparationInput.run
    {p : PhysicalModel} {ν : Measure Ln} [IsProbabilityMeasure (p.prior ν)]
    {μ : Measure Ev} [IsFiniteMeasure μ] {E : Set Ev} {G : (Fin 4 → ℤ) → Fin 3 → ℝ}
    {nativeRow : Ev → Fin 3 → ℝ} {Label : Type} [MeasurableSpace Label] {lab : Ev → Label}
    (input : RootPreparationInput p ν μ E G nativeRow lab)
    (reference : Set Ev → Set Ev)
    (hreferenceMeas : ∀ S, MeasurableSet S → S⊆E → MeasurableSet (reference S))
    (hsourceRef : ∀ S, S⊆E → S⊆reference S)
    (hreferenceTime : ∀ S, S⊆E → ∀ z∈reference S, z.2∈Icc (0:ℝ) 1) :
    ∃ U : Set (Fin 4 → ℤ), MeasurableSet U ∧
      let keep := E∩(p.physicalState input.b) ⁻¹' U
      MeasurableSet keep ∧
      μ univ ≤ (∏ i∈Finset.range input.regLength,
        ((4:ENNReal)^4*((7:ℕ)^4*⌊10^10*input.Areg^27*(input.P^3+1)⌋₊)))*
        (μ keep+ENNReal.ofReal ((300*7^8*input.H)*(input.W.card:ℝ)/input.Hprior)+
          ENNReal.ofReal ((input.Kcensus*((2:ℝ)^input.steps)^3)*((input.W.card:ℝ)*input.rate))) ∧
      (∀ z∈keep, ∀ z'∈keep, ‖G (p.physicalState input.b z)-G (p.physicalState input.b z')‖ ≤
        input.Lp*(‖p.originalPoint z-p.originalPoint z'‖+input.ρ)) ∧
      MeasurableSet {z | ¬Jets2.NativeGridQualified (reference keep) lab nativeRow input.incidence.M input.T input.mesh input.bound input.err input.duration z} ∧
      ((p.prior ν).prod volume)
        (keep\{z | Jets2.NativeGridQualified (reference keep) lab nativeRow input.incidence.M input.T input.mesh input.bound input.err input.duration z}) ≤
          input.incidence.nativeFailureBound := by
  exact prepare_original_root_qualification
    p ν input.hκ μ input.Kden input.hKden E
    input.hE input.hEp input.hfull input.hdom G input.hb input.hρ
    input.hρ1 input.hbρ input.hH input.hB input.he input.hLp input.hjets
    input.hG input.hvel input.hgraph input.hUvelocity input.hfailure input.hfailure1 input.hvelocity
    input.hstrip input.regLength input.hregLength input.regScale input.hreg0 input.hregPos input.hbreg
    input.Ar input.hAr input.hregRatio input.hregFloor input.hregNest input.regWeight input.velocityBins
    input.derivativeLists input.rhoBroad input.D input.KL input.Areg input.P input.hBroadRadius
    input.hBroadSmall input.hBroadWidth input.hD input.hAreg input.hBA input.hKLA input.hDA
    input.hcA input.hρA input.heA input.hweight input.hP input.hderiv input.hderivCard
    input.hvelocityBins input.hstateDom input.hLpReg input.W input.hresolution input.hKcensus input.hCband
    input.hrate input.hHprior input.steps input.hsteps input.hb_eq input.fineSteps input.columnSteps
    input.hwidth input.hcolumn input.hbw input.hwρ input.hround input.hgraphWidth input.hrowWidth
    input.hcensus input.hband input.Cmk input.Kfill input.hradius input.hCmk input.hMK
    input.hKfill input.hdim input.hdim1 input.hfillBudget input.hPencilWidth input.hPencilSmall input.zeta
    input.Lambda input.hzeta input.hzeta1 input.hLambda input.hworldSmall input.hworldScales input.hμ
    input.hcoeff input.hBKrow input.hRCKrow input.hFitEta input.hrowTarget input.paletteRef input.incidence
    nativeRow input.hNativeRow input.hNativeRowEq reference hreferenceMeas hsourceRef hreferenceTime
    input.T input.hTlo input.hThi input.hζT lab input.hlab input.hdiag
    input.hlabel input.mesh input.err input.duration input.bound input.hmesh input.hbound
    input.herror input.hduration

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
