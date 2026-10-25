-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.IncidenceWorldControlPreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ResidualComparisonFromIncidences
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.IncidenceWorldControl

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section

/-- Complete world control by constructing actual residual comparison
from the current incidence caps and original floors. Scalar support and
row comparison are the hereditary outputs of the preceding physical
world-row construction. No residual-comparison certificate is supplied. -/
theorem prepare_original_world_control_from_incidences {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν]
    (μ reference : Measure (Λ × ℝ)) [IsFiniteMeasure μ]
    (hμreference : μ ≤ reference)
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
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
      ‖F (parameterCode ρ (c z.1)) z.2-F (parameterCode ρ (c z'.1)) z'.2‖ ≤
        Krow*(|z.2-z'.2|+ρ))
    (hfit : ∀ z∈E, ∀ i : Fin 2,
      |G (originalFineState c b z) i.succ-F (parameterCode ρ (c z.1)) z.2 i| ≤ η)
    (hgraph : ∀ z∈E,
      |c z.1 1+2*c z.1 2*z.2-G (originalFineState c b z) 0-
        (fun i : Fin 2 => G (originalFineState c b z) i.succ) ⬝ᵥ zv (c z.1)| ≤ error)
    (L : ℕ) (hL : 1 ≤ L) (level : ℕ → ℕ) (hlevel0 : level 0=0)
    (A ζ : ℝ) (hA : 1 ≤ A)
    (hratio : ∀ i, i+1<L → dyadicParameterWidth (level i) ≤ A*dyadicParameterWidth (level (i+1)))
    (hfloorScale : dyadicParameterWidth (level (L-1)) ≤ ζ)
    (hsmall : ∀ i<L, (2+3*(H+1))*b ≤ ρ*dyadicParameterWidth (level i))
    (hρs : ∀ i<L, ρ ≤ dyadicParameterWidth (level i))
    (hosc : ∀ i<L, (2*(error+2*η*ρ)+2*(H+1)*b)/ρ ≤ dyadicParameterWidth (level i))
    {amplitude0 K0 C0 entryCut0 : ℝ} (hamp0 : 0 < amplitude0) (hK0 : 0 < K0)
    (hC0 : 0 ≤ C0) (hentryCut0 : 0 < entryCut0)
    (n0 : ℕ) (hρdyadic : ρ=dyadicParameterWidth n0)
    (amplitude K C entryCut : ℕ → ℝ)
    (hamp : ∀ i<L, 0 < amplitude i) (hK : ∀ i<L, 0 < K i) (hC : ∀ i<L, 0 ≤ C i)
    (hentryCut : ∀ i<L, 0 < entryCut i)
    (hfinite : ∀ i<L,
      ((fun z : Λ × ℝ => parameterCode (ρ*dyadicParameterWidth (level i)) (c z.1)) '' E).Finite)
    (weight0 : (Fin 2 → ℤ) → ENNReal) (hweight0 : ∀ v, weight0 v ≠ ∞)
    (weight : ℕ → (Fin 2 → ℤ) → ENNReal) (hweight : ∀ i<L, ∀ v, weight i v ≠ ∞)
    (hfloor0 : ∀ z∈E,
      ENNReal.ofReal (ρ^2*amplitude0/K0)*weight0 (parameterCode ρ (zv (c z.1))) ≤
        ν {l | parameterCode ρ (c l)=parameterCode ρ (c z.1)})
    (hfloor : ∀ i<L, ∀ z∈E,
      ENNReal.ofReal ((ρ*dyadicParameterWidth (level i))^2*amplitude i/K i)*
        weight i (parameterCode (ρ*dyadicParameterWidth (level i)) (zv (c z.1))) ≤
          ν {l | parameterCode (ρ*dyadicParameterWidth (level i)) (c l)=
            parameterCode (ρ*dyadicParameterWidth (level i)) (c z.1)})
    (hcap0 : ∀ world cell v,
      (μ.restrict E) {z | parameterCode 1 (c z.1)=world ∧
        canonicalZoomCell c 1 ρ z=cell ∧ parameterCode ρ (zv (c z.1))=v} ≤
          ENNReal.ofReal (C0*ρ*ρ^2*amplitude0)*weight0 v)
    (hcap : ∀ i<L, ∀ world cell v,
      (μ.restrict E) {z | parameterCode ρ (c z.1)=world ∧
        canonicalZoomCell c ρ (dyadicParameterWidth (level i)) z=cell ∧
        parameterCode (ρ*dyadicParameterWidth (level i)) (zv (c z.1))=v} ≤
          ENNReal.ofReal (C i*dyadicParameterWidth (level i)*
            (ρ*dyadicParameterWidth (level i))^2*amplitude i)*weight i v)
    (π : ℕ → Measure (Fin 2 → ℤ)) [∀ i, IsProbabilityMeasure (π i)]
    (Cstate : ℝ) (hCstate : 0 ≤ Cstate) (cut : ℕ → ℝ) (hcut : ∀ i<L, 0 < cut i)
    (hstateCap : ∀ i<L, ∀ q (D : Set (Fin 2 → ℤ)), MeasurableSet D →
      reference {z | originalFineState c b z=q ∧
        parameterCode (ρ*dyadicParameterWidth (level i)) (zv (c z.1))∈D} ≤
          ENNReal.ofReal Cstate*reference ((originalFineState c b) ⁻¹' {q})*π i D)
    (dimension Kss Htarget Kcap profileAmplitude : ℝ) (paletteRef : Measure (Fin 2 → ℝ))
    (hrowTarget : Krow ≤ Htarget)
    (hsupport : ∀ world t, WangZahlLot.Obl.wz_slab_local_linearity.IntervalAD ζ dimension Kss
      {x | ∃ l, (l,t)∈E ∧ parameterCode ρ (c l)=world ∧
        zS (F world) (zoomCoefficients ρ (parameterCenter ρ world) (c l)) t=x})
    (hcoarseFloor : ∀ z∈E,
      ENNReal.ofReal ((ρ^((2:ℝ)+dimension)/Kcap)*profileAmplitude)*
        paletteRef {v | parameterCode ρ v=parameterVelocityHeader (parameterCode ρ (c z.1))} ≤
        ν {l | parameterCode ρ (c l)=parameterCode ρ (c z.1)})
    (hfineFloor : ∀ r, ζ ≤ r → r ≤ 1 → ∀ z∈E,
      ENNReal.ofReal (((ρ*dyadicParameterWidth (parameterLevel r))^((2:ℝ)+dimension)/Kcap)*profileAmplitude)*
        paletteRef {v | parameterCode (ρ*dyadicParameterWidth (parameterLevel r)) v=
          parameterVelocityHeader (zoomParameterPiece ρ c r z.1)} ≤
        ν {l | zoomParameterPiece ρ c r l=zoomParameterPiece ρ c r z.1}) :
    ∃ S : Set (Λ × ℝ), MeasurableSet S ∧ S ⊆ E ∧
      μ E ≤ (∏ i∈Finset.range L,
        ((4 : ENNReal)^4*(⌈3*((C i*K i/entryCut i)*(22*Krow^2+5))*(Cstate/cut i)⌉₊+1 : ℕ))) * μ S +
          (∑ i : Fin L, ENNReal.ofReal (cut i.val)*(⌈256*(12*H+4)^7*(C0*K0/entryCut0)⌉₊*256 : ℕ))*reference univ +
          (ENNReal.ofReal (entryCut0*zoomBlockVisitConstant)+
            ∑ i : Fin L, ENNReal.ofReal (entryCut i.val*zoomBlockVisitConstant))*ν univ ∧
      OriginalWorldControl ν c S F ρ ζ dimension Htarget Kcap Kss Krow
        (2*(A+5*Krow^2)) profileAmplitude paletteRef := by
  obtain ⟨S,hS,hSE,hmass,hcomparison⟩ := original_residual_comparison_from_incidences
    ν μ reference hμreference c hc E hE G F hFm hb hρ hρ1 hbρ hH hKrow hη ht hjets
    hstateFinite hworldFinite hF hrow hfit hgraph L hL level hlevel0 A ζ hA hratio hfloorScale
    hsmall hρs hosc hamp0 hK0 hC0 hentryCut0 n0 hρdyadic amplitude K C entryCut
    hamp hK hC hentryCut hfinite weight0 hweight0 weight hweight hfloor0 hfloor hcap0 hcap
    π Cstate hCstate cut hcut hstateCap
  refine ⟨S,hS,hSE,hmass,?_⟩
  refine ⟨hFm,fun z hz => (hF z (hSE hz)).trans hrowTarget,?_,?_,?_,?_,?_⟩
  · intro world t
    apply (hsupport world t).mono
    rintro x ⟨l,hl,hw,hx⟩
    exact ⟨l,hSE hl,hw,hx⟩
  · intro z hz z' hz' hw
    exact hrow z (hSE hz) z' (hSE hz') hw
  · intro world z hz z' hz' hw hw'
    have h := hcomparison z hz z' hz' (hw.trans hw'.symm)
    simpa only [originalResidualValue,canonicalZoomCoefficients,hw,hw',zR] using h
  · intro z hz
    exact hcoarseFloor z (hSE hz)
  · intro r hr hr1 z hz
    exact hfineFloor r hr hr1 z (hSE hz)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
