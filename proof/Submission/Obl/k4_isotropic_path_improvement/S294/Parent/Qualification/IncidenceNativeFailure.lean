-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.IncidenceNativeFailure, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.IncidenceWorldControlRestrictions
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeFailureOnUnchangedSource

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section

/-- Actual current canonical numerators, full original coefficient
floors and statewise palette domination give a total native failure
bound. Spatial entry and residual comparison are both analytical only.
The physical source and witness reference are unchanged. -/
theorem native_failure_of_original_incidence_caps {Λ : Type} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsProbabilityMeasure ν]
    (μ : Measure (Λ × ℝ)) [IsFiniteMeasure μ]
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ × ℝ)) (hE : MeasurableSet E) (hμ : μ.restrict E=(ν.prod volume).restrict E)
    (G : (Fin 4 → ℤ) → Fin 3 → ℝ) (F : (Fin 7 → ℤ) → ℝ → Fin 2 → ℝ)
    (hFm : ∀ q, Measurable (F q))
    {b ρ H Krow η error : ℝ} (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hbρ : b ≤ ρ) (hH : 1 ≤ H) (hKrow : 1 ≤ Krow) (hη : 0 ≤ η)
    (ht : ∀ z∈E, z.2∈Icc (0 : ℝ) 1)
    (hjets : ∀ z∈E, |c z.1 1| ≤ H ∧ |c z.1 2| ≤ H ∧ |c z.1 4| ≤ H ∧ |c z.1 6| ≤ H)
    (hstateFinite : (originalFineState c b '' E).Finite)
    (hworldFinite : ((fun z : Λ × ℝ => parameterCode ρ (c z.1)) '' E).Finite)
    (hF : ∀ z∈E, ‖F (parameterCode ρ (c z.1)) z.2‖ ≤ Krow)
    (hrow : ∀ z∈E, ∀ z'∈E, parameterCode ρ (c z.1)=parameterCode ρ (c z'.1) →
      ‖F (parameterCode ρ (c z.1)) z.2-F (parameterCode ρ (c z'.1)) z'.2‖  ≤ 
        Krow*(|z.2-z'.2|+ρ))
    (hfit : ∀ z∈E, ∀ i : Fin 2,
      |G (originalFineState c b z) i.succ-F (parameterCode ρ (c z.1)) z.2 i| ≤ η)
    (hgraph : ∀ z∈E,
      |c z.1 1+2*c z.1 2*z.2-G (originalFineState c b z) 0-
        (fun i : Fin 2 => G (originalFineState c b z) i.succ) ⬝ᵥ zv (c z.1)| ≤ error)
    (nativeRow : Λ × ℝ → Fin 3 → ℝ) (hNativeRow : Measurable nativeRow)
    (hreadout : ∀ z∈E, nativeRow z=G (originalFineState c b z))
    (L : ℕ) (hL : 1 ≤ L) (level : ℕ → ℕ) (hlevel0 : level 0=0)
    (A ζ : ℝ) (hA : 1 ≤ A)
    (hratio : ∀ i, i+1 < L → dyadicParameterWidth (level i) ≤ A*dyadicParameterWidth (level (i+1)))
    (hfloorScale : dyadicParameterWidth (level (L-1)) ≤ ζ)
    (hsmall : ∀ i < L, (2+3*(H+1))*b ≤ ρ*dyadicParameterWidth (level i))
    (hρs : ∀ i < L, ρ ≤ dyadicParameterWidth (level i))
    (hosc : ∀ i < L, (2*(error+2*η*ρ)+2*(H+1)*b)/ρ ≤ dyadicParameterWidth (level i))
    {amplitude0 K0 C0 entryCut0 : ℝ} (hamp0 : 0 < amplitude0) (hK0 : 0 < K0)
    (hC0 : 0 ≤ C0) (hentryCut0 : 0 < entryCut0)
    (n0 : ℕ) (hρdyadic : ρ=dyadicParameterWidth n0)
    (amplitude K C entryCut : ℕ → ℝ)
    (hamp : ∀ i < L, 0 < amplitude i) (hK : ∀ i < L, 0 < K i) (hC : ∀ i < L, 0 ≤ C i)
    (hentryCut : ∀ i < L, 0 < entryCut i)
    (hfinite : ∀ i < L,
      ((fun z : Λ × ℝ => parameterCode (ρ*dyadicParameterWidth (level i)) (c z.1)) '' E).Finite)
    (weight0 : (Fin 2 → ℤ) → ENNReal) (hweight0 : ∀ v, weight0 v ≠ ∞)
    (weight : ℕ → (Fin 2 → ℤ) → ENNReal) (hweight : ∀ i < L, ∀ v, weight i v ≠ ∞)
    (hfloor0 : ∀ z∈E,
      ENNReal.ofReal (ρ^2*amplitude0/K0)*weight0 (parameterCode ρ (zv (c z.1)))  ≤ 
        ν {l | parameterCode ρ (c l)=parameterCode ρ (c z.1)})
    (hfloor : ∀ i < L, ∀ z∈E,
      ENNReal.ofReal ((ρ*dyadicParameterWidth (level i))^2*amplitude i/K i)*
        weight i (parameterCode (ρ*dyadicParameterWidth (level i)) (zv (c z.1)))  ≤ 
          ν {l | parameterCode (ρ*dyadicParameterWidth (level i)) (c l)=
            parameterCode (ρ*dyadicParameterWidth (level i)) (c z.1)})
    (hcap0 : ∀ world cell v,
      (μ.restrict E) {z | parameterCode 1 (c z.1)=world ∧
        canonicalZoomCell c 1 ρ z=cell ∧ parameterCode ρ (zv (c z.1))=v}  ≤ 
          ENNReal.ofReal (C0*ρ*ρ^2*amplitude0)*weight0 v)
    (hcap : ∀ i < L, ∀ world cell v,
      (μ.restrict E) {z | parameterCode ρ (c z.1)=world ∧
        canonicalZoomCell c ρ (dyadicParameterWidth (level i)) z=cell ∧
        parameterCode (ρ*dyadicParameterWidth (level i)) (zv (c z.1))=v}  ≤ 
          ENNReal.ofReal (C i*dyadicParameterWidth (level i)*
            (ρ*dyadicParameterWidth (level i))^2*amplitude i)*weight i v)
    (π : ℕ → Measure (Fin 2 → ℤ)) [∀ i, IsProbabilityMeasure (π i)]
    (Cstate : ℝ) (hCstate : 0 ≤ Cstate) (cut : ℕ → ℝ) (hcut : ∀ i < L, 0 < cut i)
    (hstateCap : ∀ i < L, ∀ q (D : Set (Fin 2 → ℤ)), MeasurableSet D →
      μ {z | originalFineState c b z=q ∧
        parameterCode (ρ*dyadicParameterWidth (level i)) (zv (c z.1))∈D}  ≤ 
          ENNReal.ofReal Cstate*μ ((originalFineState c b) ⁻¹' {q})*π i D)
    (dimension Kss Htarget Kcap profileAmplitude : ℝ) (paletteRef : Measure (Fin 2 → ℝ))
    (hrowTarget : Krow ≤ Htarget)
    (hsupport : ∀ world t, WangZahlLot.Obl.wz_slab_local_linearity.IntervalAD ζ dimension Kss
      {x | ∃ l, (l,t)∈E ∧ parameterCode ρ (c l)=world ∧
        zS (F world) (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t=x})
    (hcoarseFloor : ∀ z∈E,
      ENNReal.ofReal ((ρ^((2:ℝ)+dimension)/Kcap)*profileAmplitude)*
        paletteRef {v | parameterCode ρ v=parameterVelocityHeader (parameterCode ρ (c z.1))}  ≤ 
        ν {l | parameterCode ρ (c l)=parameterCode ρ (c z.1)})
    (hfineFloor : ∀ r, ζ ≤ r → r ≤ 1 → ∀ z∈E,
      ENNReal.ofReal (((ρ*dyadicParameterWidth (parameterLevel r))^((2:ℝ)+dimension)/Kcap)*profileAmplitude)*
        paletteRef {v | parameterCode (ρ*dyadicParameterWidth (parameterLevel r)) v=
          parameterVelocityHeader (zoomParameterPiece ρ c r z.1)}  ≤ 
        ν {l | zoomParameterPiece ρ c r l=zoomParameterPiece ρ c r z.1})
    {analyticEpsilon cZeta alpha Q0 N ch nativeCut nativeC : ℝ} {M : ℕ}
    (hqualification : NativeQualificationAt dimension M analyticEpsilon cZeta alpha Q0)
    (hN : 0 < N) (hch : 0 < ch) (hQ : Q0 ≤ N^ch)
    (hHtarget : Htarget=N^(ch*alpha)) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hρζ : ρ ≤ ζ)
    (hnativeCut : 0 < nativeCut) (hnativeC : 0 ≤ nativeC) (hprofile : 0 ≤ profileAmplitude)
    (hKcap : 0 < Kcap) (hnativeNum : 625*nativeC/nativeCut ≤ Kcap)
    (hcapH : 8*Kcap^2 ≤ N^(ch*alpha)) (hssH : Kss ≤ N^(ch*alpha))
    (hresH : 2*(A+5*Krow^2) ≤ N^(ch*alpha))
    (hNativeFinite : ∀ n : ℕ, n ≤ parameterLevel ζ →
      ((fun z : Λ × ℝ => originalZoomBlock c ρ (dyadicParameterWidth n) z.1) '' E).Finite)
    (hNativeCap : ∀ q : ℝ, ζ ≤ q → q ≤ 1 → ∀ world cell v,
      ((ν.prod volume).restrict E) {z | parameterCode ρ (c z.1)=world ∧
        canonicalZoomCell c ρ (dyadicParameterWidth (parameterLevel q)) z=cell ∧
        parameterCode (ρ*dyadicParameterWidth (parameterLevel q)) (zv (c z.1))=v} ≤ 
          ENNReal.ofReal (nativeC*dyadicParameterWidth (parameterLevel q)*
            (ρ*dyadicParameterWidth (parameterLevel q))^((2:ℝ)+dimension)*profileAmplitude)*
              paletteRef {v' | parameterCode (ρ*dyadicParameterWidth (parameterLevel q)) v'=v})
    (Eref : Set (Λ × ℝ)) (hEref : MeasurableSet Eref) (hEEref : E⊆Eref)
    (hErefTime : ∀ z∈Eref, z.2∈Icc (0:ℝ) 1)
    (T : ℕ)
    (hTlo : N^(-ch)/(N^(ch*alpha)) ≤ ((2:ℝ)^T)⁻¹)
    (hThi : ((2:ℝ)^T)⁻¹ ≤ (N^(ch*alpha))*N^(-ch))
    (hζT : ζ ≤ ((2:ℝ)^T)⁻¹^cZeta)
    {Label : Type} [MeasurableSpace Label] (lab : Λ × ℝ → Label)
    (hlab : Measurable lab) (hdiag : MeasurableSet {q : Label × Label | q.1=q.2})
    (hlabel : ∀ z∈E, ∀ v, (z.1,v)∈E → v∈dyadicBlock T z.2 → lab (z.1,v)=lab z)
    (mesh err duration : ℝ) (bound : ℤ) (hmesh : 0 < mesh)
    (hbound : 3*H+(1+2*H)*N^(ch*analyticEpsilon) ≤ mesh*(bound-1))
    (herror : error+(1+2*H)*(η+((2:ℝ)^T)⁻¹^((M:ℝ)+1/8))+(M+1)*mesh ≤ err)
    (hduration : duration ≤ ((2:ℝ)^T)⁻¹*N^(-(ch*analyticEpsilon))) :
    (ν.prod volume) (E\{z | NativeGridQualified Eref lab
      nativeRow M T mesh bound err duration z}) ≤ 
      ((parameterLevel ζ+1:ℕ):ENNReal)*ENNReal.ofReal (nativeCut*zoomBlockVisitConstant)+
      (∏ i∈Finset.range L,
        ((4:ENNReal)^4*(⌈3*((C i*K i/entryCut i)*(22*Krow^2+5))*(Cstate/cut i)⌉₊+1:ℕ)))*
          ENNReal.ofReal (2*N^(-(ch*alpha)))+
      (∑ i : Fin L, ENNReal.ofReal (cut i.val)*(⌈256*(12*H+4)^7*(C0*K0/entryCut0)⌉₊*256:ℕ))*μ univ+
      (ENNReal.ofReal (entryCut0*zoomBlockVisitConstant)+
        ∑ i : Fin L, ENNReal.ofReal (entryCut i.val*zoomBlockVisitConstant))*ν univ := by
  have hselection := prepare_original_world_control_on_every_restriction ν μ c hc E hE G F hFm
    hb hρ hρ1 hbρ hH hKrow hη ht hjets hstateFinite hworldFinite hF hrow hfit hgraph
    L hL level hlevel0 A ζ hA hratio hfloorScale hsmall hρs hosc hamp0 hK0 hC0 hentryCut0
    n0 hρdyadic amplitude K C entryCut hamp hK hC hentryCut hfinite
    weight0 hweight0 weight hweight hfloor0 hfloor hcap0 hcap π Cstate hCstate cut hcut hstateCap
    dimension Kss Htarget Kcap profileAmplitude paletteRef hrowTarget hsupport hcoarseFloor hfineFloor
  have hrcH : Krow ≤ N^(ch*alpha) := hrowTarget.trans_eq hHtarget
  let factor : ENNReal := ∏ i∈Finset.range L,
    ((4:ENNReal)^4*(⌈3*((C i*K i/entryCut i)*(22*Krow^2+5))*(Cstate/cut i)⌉₊+1:ℕ))
  let residualLoss : ENNReal :=
    (∑ i : Fin L, ENNReal.ofReal (cut i.val)*(⌈256*(12*H+4)^7*(C0*K0/entryCut0)⌉₊*256:ℕ))*μ univ+
    (ENNReal.ofReal (entryCut0*zoomBlockVisitConstant)+
      ∑ i : Fin L, ENNReal.ofReal (entryCut i.val*zoomBlockVisitConstant))*ν univ
  apply hqualification.failure_on_unchanged_source N ch hN hch hQ Λ ν c hc
    E Eref hE hEref hEEref hErefTime
    ρ ζ nativeCut nativeC profileAmplitude Kcap Kss Krow (2*(A+5*Krow^2))
    hρ hζ hζ1 hρζ hnativeCut hnativeC hprofile hKcap hnativeNum hcapH hssH
    (zero_le_one.trans hKrow) hrcH hresH hNativeFinite paletteRef hNativeCap
    F factor residualLoss ?_ T hTlo hThi hζT Label lab nativeRow hlab hdiag hNativeRow
    H error η (zero_le_one.trans hH) hjets ?_ (fun z hz i => by rw [hreadout z hz]; exact hfit z hz i) hlabel mesh err duration bound
    hmesh hbound herror hduration |>.trans_eq ?_
  · intro U hU hUE
    obtain ⟨selected,hselected,hselectedU,hmass,hcontrol⟩ := hselection U hU hUE
    have hmassU : μ U=(ν.prod volume) U := by
      calc
        μ U=(μ.restrict E) U := (Measure.restrict_eq_self μ hUE).symm
        _ = _ := by rw [hμ,Measure.restrict_eq_self _ hUE]
    have hmassSelected : μ selected=(ν.prod volume) selected := by
      calc
        μ selected=(μ.restrict E) selected :=
          (Measure.restrict_eq_self μ (hselectedU.trans hUE)).symm
        _ = _ := by rw [hμ,Measure.restrict_eq_self _ (hselectedU.trans hUE)]
    rw [hmassU,hmassSelected] at hmass
    refine ⟨selected,hselected,hselectedU,?_,?_⟩
    · simpa only [factor,residualLoss,add_assoc] using hmass
    · rwa [hHtarget] at hcontrol
  · intro z hz
    have hh := hgraph z hz
    rw [dot_two] at hh
    change |c z.1 1+2*c z.1 2*z.2-G (originalFineState c b z) 0-
      (G (originalFineState c b z) 1*c z.1 4+G (originalFineState c b z) 2*c z.1 6)|≤error at hh
    rw [hreadout z hz]
    convert hh using 1 <;> congr 1 <;> ring
  · simp only [factor,residualLoss,add_assoc]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
