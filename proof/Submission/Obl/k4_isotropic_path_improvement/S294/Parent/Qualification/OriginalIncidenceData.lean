-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalIncidenceData, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.IncidenceNativeFailure
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.BoundedOriginalCarriers

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- The literal original coefficient floors, current canonical-cell
numerators and fixed-reference velocity palettes used by native
qualification. There is no row, support, residual or failure certificate
in these data. They are hereditary under arbitrary source restrictions. -/
structure OriginalIncidenceData {Λ : Type} [MeasurableSpace Λ]
    (ν : Measure Λ) (μ : Measure (Λ × ℝ)) (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ))
    (b ρ H Krow η error ζ dimension Kss Htarget Kcap profileAmplitude : ℝ)
    (paletteRef : Measure (Fin 2 → ℝ)) where
  L : ℕ
  hL : 1 ≤ L
  level : ℕ → ℕ
  hlevel0 : level 0=0
  A : ℝ
  hA : 1 ≤ A
  hratio : ∀ i, i+1 < L → dyadicParameterWidth (level i) ≤ A*dyadicParameterWidth (level (i+1))
  hfloorScale : dyadicParameterWidth (level (L-1)) ≤ ζ
  hsmall : ∀ i < L, (2+3*(H+1))*b ≤ ρ*dyadicParameterWidth (level i)
  hρs : ∀ i < L, ρ ≤ dyadicParameterWidth (level i)
  hosc : ∀ i < L, (2*(error+2*η*ρ)+2*(H+1)*b)/ρ ≤ dyadicParameterWidth (level i)
  amplitude0 : ℝ
  K0 : ℝ
  C0 : ℝ
  entryCut0 : ℝ
  hamp0 : 0 < amplitude0
  hK0 : 0 < K0
  hC0 : 0 ≤ C0
  hentryCut0 : 0 < entryCut0
  n0 : ℕ
  hρdyadic : ρ=dyadicParameterWidth n0
  amplitude : ℕ → ℝ
  K : ℕ → ℝ
  C : ℕ → ℝ
  entryCut : ℕ → ℝ
  hamp : ∀ i < L, 0 < amplitude i
  hK : ∀ i < L, 0 < K i
  hC : ∀ i < L, 0 ≤ C i
  hentryCut : ∀ i < L, 0 < entryCut i
  weight0 : (Fin 2 → ℤ) → ENNReal
  hweight0 : ∀ v, weight0 v ≠ ∞
  weight : ℕ → (Fin 2 → ℤ) → ENNReal
  hweight : ∀ i < L, ∀ v, weight i v ≠ ∞
  hfloor0 : ∀ z∈E,
        ENNReal.ofReal (ρ^2*amplitude0/K0)*weight0 (parameterCode ρ (zv (c z.1)))  ≤ 
          ν {l | parameterCode ρ (c l)=parameterCode ρ (c z.1)}
  hfloor : ∀ i < L, ∀ z∈E,
        ENNReal.ofReal ((ρ*dyadicParameterWidth (level i))^2*amplitude i/K i)*
          weight i (parameterCode (ρ*dyadicParameterWidth (level i)) (zv (c z.1)))  ≤ 
            ν {l | parameterCode (ρ*dyadicParameterWidth (level i)) (c l)=
              parameterCode (ρ*dyadicParameterWidth (level i)) (c z.1)}
  hcap0 : ∀ world cell v,
        (μ.restrict E) {z | parameterCode 1 (c z.1)=world ∧
          canonicalZoomCell c 1 ρ z=cell ∧ parameterCode ρ (zv (c z.1))=v}  ≤ 
            ENNReal.ofReal (C0*ρ*ρ^2*amplitude0)*weight0 v
  hcap : ∀ i < L, ∀ world cell v,
        (μ.restrict E) {z | parameterCode ρ (c z.1)=world ∧
          canonicalZoomCell c ρ (dyadicParameterWidth (level i)) z=cell ∧
          parameterCode (ρ*dyadicParameterWidth (level i)) (zv (c z.1))=v}  ≤ 
            ENNReal.ofReal (C i*dyadicParameterWidth (level i)*
              (ρ*dyadicParameterWidth (level i))^2*amplitude i)*weight i v
  π : ℕ → Measure (Fin 2 → ℤ)
  π_probability : ∀ i, IsProbabilityMeasure (π i)
  Cstate : ℝ
  hCstate : 0 ≤ Cstate
  cut : ℕ → ℝ
  hcut : ∀ i < L, 0 < cut i
  hstateCap : ∀ i < L, ∀ q (D : Set (Fin 2 → ℤ)), MeasurableSet D →
        μ {z | originalFineState c b z=q ∧
          parameterCode (ρ*dyadicParameterWidth (level i)) (zv (c z.1))∈D}  ≤ 
            ENNReal.ofReal Cstate*μ ((originalFineState c b) ⁻¹' {q})*π i D
  hcoarseFloor : ∀ z∈E,
        ENNReal.ofReal ((ρ^((2:ℝ)+dimension)/Kcap)*profileAmplitude)*
          paletteRef {v | parameterCode ρ v=parameterVelocityHeader (parameterCode ρ (c z.1))}  ≤ 
          ν {l | parameterCode ρ (c l)=parameterCode ρ (c z.1)}
  hfineFloor : ∀ r, ζ ≤ r → r ≤ 1 → ∀ z∈E,
        ENNReal.ofReal (((ρ*dyadicParameterWidth (parameterLevel r))^((2:ℝ)+dimension)/Kcap)*profileAmplitude)*
          paletteRef {v | parameterCode (ρ*dyadicParameterWidth (parameterLevel r)) v=
            parameterVelocityHeader (zoomParameterPiece ρ c r z.1)}  ≤ 
          ν {l | zoomParameterPiece ρ c r l=zoomParameterPiece ρ c r z.1}
  analyticEpsilon : ℝ
  cZeta : ℝ
  alpha : ℝ
  Q0 : ℝ
  N : ℝ
  ch : ℝ
  nativeCut : ℝ
  nativeC : ℝ
  M : ℕ
  hqualification : NativeQualificationAt dimension M analyticEpsilon cZeta alpha Q0
  hN : 0 < N
  hch : 0 < ch
  hQ : Q0 ≤ N^ch
  hHtarget : Htarget=N^(ch*alpha)
  hζ : 0 < ζ
  hζ1 : ζ ≤ 1
  hρζ : ρ ≤ ζ
  hnativeCut : 0 < nativeCut
  hnativeC : 0 ≤ nativeC
  hprofile : 0 ≤ profileAmplitude
  hKcap : 0 < Kcap
  hnativeNum : 625*nativeC/nativeCut ≤ Kcap
  hcapH : 8*Kcap^2 ≤ N^(ch*alpha)
  hssH : Kss ≤ N^(ch*alpha)
  hresH : 2*(A+5*Krow^2) ≤ N^(ch*alpha)
  hNativeCap : ∀ q : ℝ, ζ ≤ q → q ≤ 1 → ∀ world cell v,
        ((ν.prod volume).restrict E) {z | parameterCode ρ (c z.1)=world ∧
          canonicalZoomCell c ρ (dyadicParameterWidth (parameterLevel q)) z=cell ∧
          parameterCode (ρ*dyadicParameterWidth (parameterLevel q)) (zv (c z.1))=v} ≤ 
            ENNReal.ofReal (nativeC*dyadicParameterWidth (parameterLevel q)*
              (ρ*dyadicParameterWidth (parameterLevel q))^((2:ℝ)+dimension)*profileAmplitude)*
                paletteRef {v' | parameterCode (ρ*dyadicParameterWidth (parameterLevel q)) v'=v}

/-- Restriction preserves every original reference and palette. Only
current numerator measures and pointwise source sets get smaller. -/
def OriginalIncidenceData.restrict {Λ : Type} [MeasurableSpace Λ] {ν : Measure Λ} {μ : Measure (Λ × ℝ)}
    {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)}
    {b ρ H Krow η error ζ dimension Kss Htarget Kcap profileAmplitude : ℝ}
    {paletteRef : Measure (Fin 2 → ℝ)}
    (data : OriginalIncidenceData ν μ c E b ρ H Krow η error ζ dimension Kss Htarget Kcap profileAmplitude paletteRef)
    {S : Set (Λ × ℝ)} (hSE : S⊆E) :
    OriginalIncidenceData ν μ c S b ρ H Krow η error ζ dimension Kss Htarget Kcap profileAmplitude paletteRef where
  L := data.L
  hL := data.hL
  level := data.level
  hlevel0 := data.hlevel0
  A := data.A
  hA := data.hA
  hratio := data.hratio
  hfloorScale := data.hfloorScale
  hsmall := data.hsmall
  hρs := data.hρs
  hosc := data.hosc
  amplitude0 := data.amplitude0
  K0 := data.K0
  C0 := data.C0
  entryCut0 := data.entryCut0
  hamp0 := data.hamp0
  hK0 := data.hK0
  hC0 := data.hC0
  hentryCut0 := data.hentryCut0
  n0 := data.n0
  hρdyadic := data.hρdyadic
  amplitude := data.amplitude
  K := data.K
  C := data.C
  entryCut := data.entryCut
  hamp := data.hamp
  hK := data.hK
  hC := data.hC
  hentryCut := data.hentryCut
  weight0 := data.weight0
  hweight0 := data.hweight0
  weight := data.weight
  hweight := data.hweight
  hfloor0 := fun z hz => data.hfloor0 z (hSE hz)
  hfloor := fun i hi z hz => data.hfloor i hi z (hSE hz)
  hcap0 := by
    intro world cell v
    exact (Measure.restrict_mono hSE le_rfl _).trans (data.hcap0 world cell v)
  hcap := by
    intro i hi world cell v
    exact (Measure.restrict_mono hSE le_rfl _).trans (data.hcap i hi world cell v)
  π := data.π
  π_probability := data.π_probability
  Cstate := data.Cstate
  hCstate := data.hCstate
  cut := data.cut
  hcut := data.hcut
  hstateCap := data.hstateCap
  hcoarseFloor := fun z hz => data.hcoarseFloor z (hSE hz)
  hfineFloor := fun r hr hr1 z hz => data.hfineFloor r hr hr1 z (hSE hz)
  analyticEpsilon := data.analyticEpsilon
  cZeta := data.cZeta
  alpha := data.alpha
  Q0 := data.Q0
  N := data.N
  ch := data.ch
  nativeCut := data.nativeCut
  nativeC := data.nativeC
  M := data.M
  hqualification := data.hqualification
  hN := data.hN
  hch := data.hch
  hQ := data.hQ
  hHtarget := data.hHtarget
  hζ := data.hζ
  hζ1 := data.hζ1
  hρζ := data.hρζ
  hnativeCut := data.hnativeCut
  hnativeC := data.hnativeC
  hprofile := data.hprofile
  hKcap := data.hKcap
  hnativeNum := data.hnativeNum
  hcapH := data.hcapH
  hssH := data.hssH
  hresH := data.hresH
  hNativeCap := by
    intro q hq hq1 world cell v
    exact (Measure.restrict_mono hSE le_rfl _).trans (data.hNativeCap q hq hq1 world cell v)


section Bounds

variable {Λ : Type} [MeasurableSpace Λ] {ν : Measure Λ} {μ : Measure (Λ × ℝ)}
    {c : Λ → Fin 7 → ℝ} {E : Set (Λ × ℝ)}
    {b ρ H Krow η error ζ dimension Kss Htarget Kcap profileAmplitude : ℝ}
    {paletteRef : Measure (Fin 2 → ℝ)}
    (data : OriginalIncidenceData ν μ c E b ρ H Krow η error ζ dimension Kss Htarget Kcap profileAmplitude paletteRef)

def OriginalIncidenceData.selectionFactor : ENNReal :=
  ∏ i∈Finset.range data.L,
    ((4:ENNReal)^4*(⌈3*((data.C i*data.K i/data.entryCut i)*(22*Krow^2+5))*(data.Cstate/data.cut i)⌉₊+1:ℕ))

def OriginalIncidenceData.residualEntryLoss : ENNReal :=
  (∑ i : Fin data.L, ENNReal.ofReal (data.cut i.val)*
    (⌈256*(12*H+4)^7*(data.C0*data.K0/data.entryCut0)⌉₊*256:ℕ))*μ univ+
  (ENNReal.ofReal (data.entryCut0*zoomBlockVisitConstant)+
    ∑ i : Fin data.L, ENNReal.ofReal (data.entryCut i.val*zoomBlockVisitConstant))*ν univ

def OriginalIncidenceData.nativeFailureBound : ENNReal :=
  ((parameterLevel ζ+1:ℕ):ENNReal)*ENNReal.ofReal (data.nativeCut*zoomBlockVisitConstant)+
    data.selectionFactor*ENNReal.ofReal (2*data.N^(-(data.ch*data.alpha)))+data.residualEntryLoss

/-- The original incidence data construct residual comparison inside
failure analysis. All finite carriers are derived from bounded original
coefficients. The source and the displayed native row are unchanged. -/
theorem OriginalIncidenceData.failure [IsProbabilityMeasure ν] [IsFiniteMeasure μ]
    (hc : Measurable c) (hE : MeasurableSet E)
    (hμ : μ.restrict E=(ν.prod volume).restrict E)
    (G : (Fin 4 → ℤ) → Fin 3 → ℝ) (F : (Fin 7 → ℤ) → ℝ → Fin 2 → ℝ)
    (hFm : ∀ world, Measurable (F world))
    (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbρ : b ≤ ρ)
    (hH : 1 ≤ H) (hKrow : 1 ≤ Krow) (hη : 0 ≤ η)
    (ht : ∀ z∈E, z.2∈Icc (0:ℝ) 1) (hcoeff : ∀ z∈E, ∀ j, |c z.1 j| ≤ H)
    (hF : ∀ z∈E, ‖F (parameterCode ρ (c z.1)) z.2‖ ≤ Krow)
    (hrow : ∀ z∈E, ∀ z'∈E, parameterCode ρ (c z.1)=parameterCode ρ (c z'.1) →
      ‖F (parameterCode ρ (c z.1)) z.2-F (parameterCode ρ (c z'.1)) z'.2‖ ≤
        Krow*(|z.2-z'.2|+ρ))
    (hfit : ∀ z∈E, ∀ i : Fin 2,
      |G (originalFineState c b z) i.succ-F (parameterCode ρ (c z.1)) z.2 i| ≤ η)
    (hgraph : ∀ z∈E,
      |c z.1 1+2*c z.1 2*z.2-G (originalFineState c b z) 0-
        (fun i : Fin 2 => G (originalFineState c b z) i.succ) ⬝ᵥ zv (c z.1)| ≤ error)
    (nativeRow : Λ × ℝ → Fin 3 → ℝ) (hNativeRow : Measurable nativeRow)
    (hreadout : ∀ z∈E, nativeRow z=G (originalFineState c b z))
    (hrowTarget : Krow ≤ Htarget)
    (hsupport : ∀ world t, WangZahlLot.Obl.wz_slab_local_linearity.IntervalAD ζ dimension Kss
      {x | ∃ l, (l,t)∈E ∧ parameterCode ρ (c l)=world ∧
        zS (F world) (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t=x})
    (Eref : Set (Λ × ℝ)) (hEref : MeasurableSet Eref) (hEEref : E⊆Eref)
    (hErefTime : ∀ z∈Eref, z.2∈Icc (0:ℝ) 1)
    (T : ℕ)
    (hTlo : data.N^(-data.ch)/(data.N^(data.ch*data.alpha)) ≤ ((2:ℝ)^T)⁻¹)
    (hThi : ((2:ℝ)^T)⁻¹ ≤ (data.N^(data.ch*data.alpha))*data.N^(-data.ch))
    (hζT : ζ ≤ ((2:ℝ)^T)⁻¹^data.cZeta)
    {Label : Type} [MeasurableSpace Label] (lab : Λ × ℝ → Label)
    (hlab : Measurable lab) (hdiag : MeasurableSet {q : Label × Label | q.1=q.2})
    (hlabel : ∀ z∈E, ∀ v, (z.1,v)∈E → v∈dyadicBlock T z.2 → lab (z.1,v)=lab z)
    (mesh err duration : ℝ) (bound : ℤ) (hmesh : 0 < mesh)
    (hbound : 3*H+(1+2*H)*data.N^(data.ch*data.analyticEpsilon) ≤ mesh*(bound-1))
    (herror : error+(1+2*H)*(η+((2:ℝ)^T)⁻¹^((data.M:ℝ)+1/8))+(data.M+1)*mesh ≤ err)
    (hduration : duration ≤ ((2:ℝ)^T)⁻¹*data.N^(-(data.ch*data.analyticEpsilon))) :
    (ν.prod volume) (E\{z | NativeGridQualified Eref lab nativeRow data.M T mesh bound err duration z}) ≤
      data.nativeFailureBound := by
  letI : ∀ i, IsProbabilityMeasure (data.π i) := data.π_probability
  have hfinite := fun i => finite_original_parameter_image_of_bounded c E
    (mul_pos hρ (dyadicParameterWidth_pos (data.level i))) hcoeff
  have hNativeFinite := fun n => finite_original_zoom_block_image_of_bounded c E hρ hcoeff n
  have hfailed := native_failure_of_original_incidence_caps ν μ c hc E hE hμ G F hFm
    hb hρ hρ1 hbρ hH hKrow hη ht
    (fun z hz => ⟨hcoeff z hz 1,hcoeff z hz 2,hcoeff z hz 4,hcoeff z hz 6⟩)
    (finite_original_fine_state_image_of_bounded c E hH hb ht hcoeff)
    (finite_original_parameter_image_of_bounded c E hρ hcoeff) hF hrow hfit hgraph
    nativeRow hNativeRow hreadout data.L data.hL data.level data.hlevel0 data.A ζ data.hA
    data.hratio data.hfloorScale data.hsmall data.hρs data.hosc
    data.hamp0 data.hK0 data.hC0 data.hentryCut0 data.n0 data.hρdyadic
    data.amplitude data.K data.C data.entryCut data.hamp data.hK data.hC data.hentryCut
    (fun i _ => hfinite i) data.weight0 data.hweight0 data.weight data.hweight data.hfloor0
    data.hfloor data.hcap0 data.hcap data.π data.Cstate data.hCstate data.cut data.hcut data.hstateCap
    dimension Kss Htarget Kcap profileAmplitude paletteRef hrowTarget hsupport data.hcoarseFloor data.hfineFloor
    data.hqualification data.hN data.hch data.hQ data.hHtarget data.hζ data.hζ1 data.hρζ
    data.hnativeCut data.hnativeC data.hprofile data.hKcap data.hnativeNum data.hcapH data.hssH data.hresH
    (fun n _ => hNativeFinite n) data.hNativeCap Eref hEref hEEref hErefTime T hTlo hThi hζT
    lab hlab hdiag hlabel mesh err duration bound hmesh hbound herror hduration
  simpa only [OriginalIncidenceData.nativeFailureBound,OriginalIncidenceData.selectionFactor,
    OriginalIncidenceData.residualEntryLoss,add_assoc] using hfailed

end Bounds

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
