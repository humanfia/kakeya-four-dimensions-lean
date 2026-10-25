-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ResidualComparisonFromIncidences, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/ResidualComparisonFromIncidences.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265/x1027, commit9990050b,
Broad/Qualification/ResidualComparisonFromSnapshots.lean, ported by o287/x1035.
The snapshot supplier is replaced by original current-entry pruning. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.SimultaneousIncidenceParameterPalettes
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DyadicParameterPaletteCoarsening
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.FourJetPreparedResidualComparison

/-! # Direct original residual preparation from current incidence caps

All coarse and fine parameter palettes, residual tables, entry floors
and posterior laws are constructed. The original measure stays fixed.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section

theorem original_residual_comparison_from_incidences {Λ : Type*} [MeasurableSpace Λ]
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
          ENNReal.ofReal Cstate*reference ((originalFineState c b) ⁻¹' {q})*π i D) :
    ∃ S : Set (Λ × ℝ), MeasurableSet S ∧ S ⊆ E ∧
      μ E ≤ (∏ i∈Finset.range L,
        ((4 : ENNReal)^4*(⌈3*((C i*K i/entryCut i)*(22*Krow^2+5))*(Cstate/cut i)⌉₊+1 : ℕ))) * μ S +
          (∑ i : Fin L, ENNReal.ofReal (cut i.val)*(⌈256*(12*H+4)^7*(C0*K0/entryCut0)⌉₊*256 : ℕ))*reference univ +
          (ENNReal.ofReal (entryCut0*zoomBlockVisitConstant)+
            ∑ i : Fin L, ENNReal.ofReal (entryCut i.val*zoomBlockVisitConstant))*ν univ ∧
      ∀ z∈S, ∀ z'∈S, parameterCode ρ (c z.1)=parameterCode ρ (c z'.1) →
        |originalResidualValue (fun y => canonicalZoomCoefficients c ρ y.1)
          (fun y => F (parameterCode ρ (c y.1)) y.2) Prod.snd z-
          originalResidualValue (fun y => canonicalZoomCoefficients c ρ y.1)
            (fun y => F (parameterCode ρ (c y.1)) y.2) Prod.snd z'| ≤
              2*(A+5*Krow^2)*(‖zpos (canonicalZoomCoefficients c ρ z.1) z.2-
                zpos (canonicalZoomCoefficients c ρ z'.1) z'.2‖+ζ) := by
  classical
  let s := fun i => dyadicParameterWidth (level i)
  have hsmall0 : (2+3*(H+1))*b ≤ ρ := by
    simpa only [s,hlevel0,dyadicParameterWidth,pow_zero,inv_one,mul_one] using hsmall 0 hL
  obtain ⟨E',hE',hsub,hloss,blocks,palettes,hblocksCard,hcard,hblocksKnown,hknown⟩ :=
    prepare_simultaneous_incidence_parameter_palettes μ ν c hc E hE
      hb (hbρ.trans hρ1) hρ (by linarith) hamp0 hK0 hC0 hentryCut0 n0 hρdyadic
      (fun i : Fin L => level i.val) (fun i => amplitude i.val) (fun i => K i.val)
      (fun i => C i.val) (fun i => entryCut i.val)
      (fun i => hamp i.val i.isLt) (fun i => hK i.val i.isLt)
      (fun i => hC i.val i.isLt) (fun i => hentryCut i.val i.isLt)
      ht hjets hsmall0 hworldFinite (fun i => hfinite i.val i.isLt)
      weight0 hweight0 (fun i => weight i.val) (fun i => hweight i.val i.isLt)
      hfloor0 (fun i => hfloor i.val i.isLt) hcap0 (fun i => hcap i.val i.isLt)
  have hmassSplit : μ E=μ E'+μ (E \ E') := by
    have hh := measure_add_sdiff (μ := μ) hE'.nullMeasurableSet E
    rw [union_eq_right.mpr hsub] at hh
    exact hh.symm
  let finePalettes := fun i : ℕ => if hi : i<L then palettes ⟨i,hi⟩ else fun _ => ∅
  have hblockCard (q) : (blocks q).card ≤ ⌈256*(12*H+4)^7*(C0*K0/entryCut0)⌉₊ := by
    exact_mod_cast (hblocksCard q).trans (Nat.le_ceil (256*(12*H+4)^7*(C0*K0/entryCut0)))
  have hblocks (z : Λ × ℝ) (hz : z∈E') : parameterCode ρ (c z.1) ∈
      blocks (originalFineState c b z,![parameterCode ρ (c z.1) 4,parameterCode ρ (c z.1) 6]) := by
    convert hblocksKnown z hz using 1 <;> congr 2
    funext i
    fin_cases i <;> rfl
  have hFineCard (i : ℕ) (hi : i<L) (q) : ((finePalettes i q).card : ℝ) ≤ C i*K i/entryCut i := by
    simpa only [finePalettes,dite_eq_left hi] using hcard ⟨i,hi⟩ q
  have hFineKnown (i : ℕ) (hi : i<L) (z : Λ × ℝ) (hz : z∈E') :
      parameterCode (ρ*s i) (c z.1) ∈ finePalettes i
        ((parameterCode ρ (c z.1),canonicalZoomCell c ρ (s i) z),parameterCode (ρ*s i) (zv (c z.1))) := by
    simpa only [finePalettes,dite_eq_left hi] using hknown ⟨i,hi⟩ z hz
  have hvm : Measurable (fun l => zv (c l)) := by
    apply measurable_pi_iff.mpr
    intro j
    fin_cases j
    · change Measurable (fun l => c l 4)
      exact (measurable_pi_apply 4).comp hc
    · change Measurable (fun l => c l 6)
      exact (measurable_pi_apply 6).comp hc
  obtain ⟨S,hS,hSE',hmass,hcmp⟩ := original_prepared_residual_comparison_of_jets μ reference
    hμreference E' hE' c hc G F hFm b ρ H Krow η error hb hρ hρ1 (by linarith) hKrow hη
    (fun z hz => ht z (hsub hz)) (fun z hz => hjets z (hsub hz))
    (hstateFinite.subset (image_mono hsub)) (hworldFinite.subset (image_mono hsub))
    (fun z hz => hF z (hsub hz))
    (fun z hz z' hz' => hrow z (hsub hz) z' (hsub hz'))
    (fun z hz => hfit z (hsub hz)) (fun z hz => hgraph z (hsub hz))
    L hL s A ζ hA (by simp only [s,hlevel0,dyadicParameterWidth,pow_zero,inv_one])
    (fun i => dyadicParameterWidth_pos _) hratio hfloorScale hsmall hρs hosc
    (fun q => ![q 4,q 6]) blocks ⌈256*(12*H+4)^7*(C0*K0/entryCut0)⌉₊ hblockCard hblocks
    (fun i l => parameterCode (ρ*s i) (zv (c l)))
    (fun i => (measurable_parameterCode (ρ*s i)).comp hvm)
    π (fun i => dyadicPaletteParent (level i)) (fun i => measurable_dyadicPaletteParent _)
    (fun i _ z _ => dyadicPaletteParent_velocity_header (level i) hρ (c z.1))
    Cstate hCstate cut (fun i => C i*K i/entryCut i) hcut
    (fun i hi => div_nonneg (mul_nonneg (hC i hi) (hK i hi).le) (hentryCut i hi).le) hstateCap
    finePalettes hFineCard hFineKnown
  refine ⟨S,hS,hSE'.trans hsub,?_,hcmp⟩
  rw [hmassSplit]
  exact add_le_add hmass hloss

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
