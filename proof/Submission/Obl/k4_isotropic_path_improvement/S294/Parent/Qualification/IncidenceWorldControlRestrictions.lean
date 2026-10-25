-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.IncidenceWorldControlRestrictions, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.IncidenceWorldControlPreparation

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section

/-- Every hypothetical restriction admits actual residual comparison
with a uniform selection cost, from the SAME full-source incidence
caps, original floors and hereditary scalar support. This lets residual
selection be used inside a failure argument without cutting the final
source or changing its statewise breadth. -/
theorem prepare_original_world_control_on_every_restriction {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν]
    (μ : Measure (Λ × ℝ)) [IsFiniteMeasure μ]
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
      μ {z | originalFineState c b z=q ∧
        parameterCode (ρ*dyadicParameterWidth (level i)) (zv (c z.1))∈D} ≤
          ENNReal.ofReal Cstate*μ ((originalFineState c b) ⁻¹' {q})*π i D)
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
    ∀ U : Set (Λ × ℝ), MeasurableSet U → U⊆E →
    ∃ S : Set (Λ × ℝ), MeasurableSet S ∧ S ⊆ U ∧
      μ U ≤ (∏ i∈Finset.range L,
        ((4 : ENNReal)^4*(⌈3*((C i*K i/entryCut i)*(22*Krow^2+5))*(Cstate/cut i)⌉₊+1 : ℕ))) * μ S +
          (∑ i : Fin L, ENNReal.ofReal (cut i.val)*(⌈256*(12*H+4)^7*(C0*K0/entryCut0)⌉₊*256 : ℕ))*μ univ +
          (ENNReal.ofReal (entryCut0*zoomBlockVisitConstant)+
            ∑ i : Fin L, ENNReal.ofReal (entryCut i.val*zoomBlockVisitConstant))*ν univ ∧
      OriginalWorldControl ν c S F ρ ζ dimension Htarget Kcap Kss Krow
        (2*(A+5*Krow^2)) profileAmplitude paletteRef := by
  intro U hU hUE
  have hcurId : (μ.restrict U).restrict U=μ.restrict U :=
    Measure.restrict_restrict_of_subset (Subset.refl U)
  have hcap0U (world) (cell) (v) :
      ((μ.restrict U).restrict U) {z | parameterCode 1 (c z.1)=world ∧
        canonicalZoomCell c 1 ρ z=cell ∧ parameterCode ρ (zv (c z.1))=v} ≤
          ENNReal.ofReal (C0*ρ*ρ^2*amplitude0)*weight0 v := by
    rw [hcurId]
    exact (Measure.restrict_mono hUE le_rfl _).trans (hcap0 world cell v)
  have hcapU (i) (hi : i<L) (world) (cell) (v) :
      ((μ.restrict U).restrict U) {z | parameterCode ρ (c z.1)=world ∧
        canonicalZoomCell c ρ (dyadicParameterWidth (level i)) z=cell ∧
        parameterCode (ρ*dyadicParameterWidth (level i)) (zv (c z.1))=v} ≤
          ENNReal.ofReal (C i*dyadicParameterWidth (level i)*
            (ρ*dyadicParameterWidth (level i))^2*amplitude i)*weight i v := by
    rw [hcurId]
    exact (Measure.restrict_mono hUE le_rfl _).trans (hcap i hi world cell v)
  obtain ⟨S,hS,hSU,hmass,hcontrol⟩ := prepare_original_world_control_from_incidences
    ν (μ.restrict U) μ Measure.restrict_le_self c hc U hU G F hFm hb hρ hρ1 hbρ hH hKrow hη
    (fun z hz => ht z (hUE hz)) (fun z hz => hjets z (hUE hz))
    (hstateFinite.subset (Set.image_mono hUE)) (hworldFinite.subset (Set.image_mono hUE))
    (fun z hz => hF z (hUE hz)) (fun z hz z' hz' => hrow z (hUE hz) z' (hUE hz'))
    (fun z hz => hfit z (hUE hz)) (fun z hz => hgraph z (hUE hz))
    L hL level hlevel0 A ζ hA hratio hfloorScale hsmall hρs hosc hamp0 hK0 hC0 hentryCut0
    n0 hρdyadic amplitude K C entryCut hamp hK hC hentryCut
    (fun i hi => (hfinite i hi).subset (Set.image_mono hUE))
    weight0 hweight0 weight hweight (fun z hz => hfloor0 z (hUE hz))
    (fun i hi z hz => hfloor i hi z (hUE hz)) hcap0U hcapU
    π Cstate hCstate cut hcut hstateCap dimension Kss Htarget Kcap profileAmplitude paletteRef
    hrowTarget (by
      intro world t
      apply (hsupport world t).mono
      rintro x ⟨l,hl,hw,hx⟩
      exact ⟨l,hUE hl,hw,hx⟩)
    (fun z hz => hcoarseFloor z (hUE hz)) (fun r hr hr1 z hz => hfineFloor r hr hr1 z (hUE hz))
  refine ⟨S,hS,hSU,?_,hcontrol⟩
  simpa only [Measure.restrict_eq_self μ (Subset.refl U),Measure.restrict_eq_self μ hSU] using hmass

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
