-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.OriginalRootPreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.RowWorldSupportPreparation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalIncidenceData
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativeQualification

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

/-- Construct physical row regularity, all world scalar supports and
the total native exception together. The final source consists only of
whole original fine states; both spatial and residual qualification
selections are used solely inside the failure proof. The witness
reference is formed from the final physical source. -/
theorem prepare_original_root_qualification (p : PhysicalModel) (ν : Measure Ln)
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
    (hworldScales : ∀ r : ℝ, zeta ≤ r → r ≤ 1 → ∃ w∈W, w ≤ ρ*r ∧ ρ*r ≤ Lambda*w)
    (hμ : μ=((p.prior ν).prod volume).restrict E)
    (hcoeff : ∀ l∈p.assigned, ∀ j, |p.scalarCoefficients l j| ≤ H)
    {Krow eta Htarget Kcap profileAmplitude : ℝ}
    (hBKrow : B ≤ Krow) (hRCKrow : 3*((3*H+1)*Lp) ≤ Krow)
    (hFitEta : 2*((3*H+1)*Lp)*ρ ≤ eta) (hrowTarget : Krow ≤ Htarget)
    (paletteRef : Measure (Fin 2 → ℝ))
    (incidence : Jets2.OriginalIncidenceData (p.prior ν) μ p.scalarCoefficients E
      b ρ H Krow eta error zeta dimension (worldScalarSupportConstant B Cband rate Kfill Lambda)
      Htarget Kcap profileAmplitude paletteRef)
    (nativeRow : Ev → Fin 3 → ℝ) (hNativeRow : Measurable nativeRow)
    (hNativeRowEq : ∀ z∈E, nativeRow z=G (p.physicalState b z))
    (reference : Set Ev → Set Ev)
    (hreferenceMeas : ∀ S, MeasurableSet S → S⊆E → MeasurableSet (reference S))
    (hsourceRef : ∀ S, S⊆E → S⊆reference S)
    (hreferenceTime : ∀ S, S⊆E → ∀ z∈reference S, z.2∈Icc (0:ℝ) 1)
    (T : ℕ)
    (hTlo : incidence.N^(-incidence.ch)/(incidence.N^(incidence.ch*incidence.alpha)) ≤ ((2:ℝ)^T)⁻¹)
    (hThi : ((2:ℝ)^T)⁻¹ ≤ (incidence.N^(incidence.ch*incidence.alpha))*incidence.N^(-incidence.ch))
    (hζT : zeta ≤ ((2:ℝ)^T)⁻¹^incidence.cZeta)
    {Label : Type} [MeasurableSpace Label] (lab : Ev → Label)
    (hlab : Measurable lab) (hdiag : MeasurableSet {q : Label × Label | q.1=q.2})
    (hlabel : ∀ z∈E, ∀ v, (z.1,v)∈E → v∈Jets2.dyadicBlock T z.2 → lab (z.1,v)=lab z)
    (mesh err duration : ℝ) (bound : ℤ) (hmesh : 0 < mesh)
    (hbound : 3*H+(1+2*H)*incidence.N^(incidence.ch*incidence.analyticEpsilon) ≤ mesh*(bound-1))
    (herror : error+(1+2*H)*(eta+((2:ℝ)^T)⁻¹^((incidence.M:ℝ)+1/8))+(incidence.M+1)*mesh ≤ err)
    (hduration : duration ≤ ((2:ℝ)^T)⁻¹*incidence.N^(-(incidence.ch*incidence.analyticEpsilon))) :
    ∃ U : Set (Fin 4 → ℤ), MeasurableSet U ∧
      let keep := E∩(p.physicalState b) ⁻¹' U
      MeasurableSet keep ∧
      μ univ ≤ (∏ i∈Finset.range regLength,
        ((4:ENNReal)^4*((7:ℕ)^4*⌊10^10*Areg^27*(P^3+1)⌋₊)))*
        (μ keep+ENNReal.ofReal ((300*7^8*H)*(W.card:ℝ)/Hprior)+
          ENNReal.ofReal ((Kcensus*((2:ℝ)^steps)^3)*((W.card:ℝ)*rate))) ∧
      (∀ z∈keep, ∀ z'∈keep, ‖G (p.physicalState b z)-G (p.physicalState b z')‖ ≤
        Lp*(‖p.originalPoint z-p.originalPoint z'‖+ρ)) ∧
      MeasurableSet {z | ¬Jets2.NativeGridQualified (reference keep) lab nativeRow incidence.M T mesh bound err duration z} ∧
      ((p.prior ν).prod volume)
        (keep\{z | Jets2.NativeGridQualified (reference keep) lab nativeRow incidence.M T mesh bound err duration z}) ≤
          incidence.nativeFailureBound := by
  obtain ⟨U,F,hU,hkeep,hmass,hLip,hFm,hFb,hFfit,hRC,hSS⟩ :=
    prepare_original_row_world_support p ν hκ μ Kden hKden E hE hEp hfull hdom G hb hρ hρ1 hbρ
      hH hB he hLp hjets hG hvel hgraph hUvelocity hfailure hfailure1 hvelocity hstrip
      regLength hregLength regScale hreg0 hregPos hbreg Ar hAr hregRatio hregFloor hregNest
      regWeight velocityBins derivativeLists rhoBroad D KL Areg P hBroadRadius hBroadSmall hBroadWidth
      hD hAreg hBA hKLA hDA hcA hρA heA hweight hP hderiv hderivCard hvelocityBins hstateDom hLpReg
      W hresolution hKcensus hCband hrate hHprior steps hsteps hb_eq fineSteps columnSteps
      hwidth hcolumn hbw hwρ hround hgraphWidth hrowWidth hcensus hband Cmk Kfill hradius hCmk hMK
      hKfill hdim hdim1 hfillBudget hPencilWidth hPencilSmall zeta Lambda hzeta hzeta1 hLambda
      hworldSmall hworldScales
  let keep := E∩(p.physicalState b) ⁻¹' U
  have hkeepE : keep⊆E := inter_subset_left
  have hEpkeep : keep⊆p.event := hkeepE.trans hEp
  have href : MeasurableSet (reference keep) := hreferenceMeas keep hkeep hkeepE
  have hgood : MeasurableSet {z | Jets2.NativeGridQualified (reference keep) lab nativeRow incidence.M
      T mesh bound err duration z} :=
    Jets2.measurableSet_nativeGridQualified href hlab hdiag hNativeRow incidence.M T mesh bound err duration
  refine ⟨U,hU,hkeep,hmass,hLip,hgood.compl,?_⟩
  let scalarG : (Fin 4 → ℤ) → Fin 3 → ℝ := G ∘ scalarStateToPhysical
  have hscalarG (z : Ev) : scalarG (Jets2.originalFineState p.scalarCoefficients b z)=G (p.physicalState b z) :=
    congrArg G (p.physicalState_eq_scalarState b z).symm
  have hgraphScalar : ∀ z∈keep,
      |p.scalarCoefficients z.1 1+2*p.scalarCoefficients z.1 2*z.2-
        scalarG (Jets2.originalFineState p.scalarCoefficients b z) 0-
          (fun i : Fin 2 => scalarG (Jets2.originalFineState p.scalarCoefficients b z) i.succ) ⬝ᵥ
            Jets2.zv (p.scalarCoefficients z.1)| ≤ error := by
    intro z hz
    rw [hscalarG,Jets2.dot_two]
    have hh := hgraph z (hkeepE hz)
    rw [p.velocity_graph_eq] at hh
    change |p.scalarCoefficients z.1 1+2*p.scalarCoefficients z.1 2*z.2-G (p.physicalState b z) 0-
      (G (p.physicalState b z) 1*p.scalarCoefficients z.1 4+
        G (p.physicalState b z) 2*p.scalarCoefficients z.1 6)| ≤ error
    convert hh using 1 <;> congr 1 <;> ring
  have hfitScalar : ∀ z∈keep, ∀ i : Fin 2,
      |scalarG (Jets2.originalFineState p.scalarCoefficients b z) i.succ-
        F (Jets2.parameterCode ρ (p.scalarCoefficients z.1)) z.2 i| ≤ eta := by
    intro z hz i
    rw [hscalarG]
    have hh := (norm_le_pi_norm _ i).trans ((hFfit z hz).trans hFitEta)
    simpa only [Pi.sub_apply,Real.norm_eq_abs,abs_sub_comm] using hh
  have hμkeep : μ.restrict keep=((p.prior ν).prod volume).restrict keep := by
    rw [hμ,Measure.restrict_restrict_of_subset hkeepE]
  have hEta : 0 ≤ eta := (by positivity : (0:ℝ) ≤ 2*((3*H+1)*Lp)*ρ).trans hFitEta
  have hfailed := (incidence.restrict hkeepE).failure p.measurable_scalarCoefficients hkeep hμkeep
    scalarG F hFm hb hρ hρ1 hbρ hH (hB.trans hBKrow) hEta
    (fun z hz => p.event_time z (hEpkeep hz))
    (fun z hz => hcoeff z.1 (p.event_assignment z (hEpkeep hz)))
    (fun z hz => (hFb z hz).trans hBKrow)
    (by
      intro z hz z' hz' heq
      exact (hRC z hz z' hz' heq).trans
        (mul_le_mul_of_nonneg_right hRCKrow (by positivity)))
    hfitScalar hgraphScalar nativeRow hNativeRow
    (fun z hz => (hNativeRowEq z (hkeepE hz)).trans (hscalarG z).symm)
    hrowTarget (hSS keep (Subset.refl keep))
    (reference keep) href (hsourceRef keep hkeepE) (hreferenceTime keep hkeepE)
    T hTlo hThi hζT lab hlab hdiag
    (fun z hz v hv => hlabel z (hkeepE hz) v (hkeepE hv))
    mesh err duration bound hmesh hbound herror hduration
  exact hfailed

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
