-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.OriginalResidualPreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/OriginalResidualPreparation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/OriginalResidualPreparation.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/OriginalResidualPreparation.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalZoomEntryFloors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.WorldResidualSelection


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory
open scoped BigOperators

noncomputable section

/-- Actual original entry cleanup and common-palette summation produce
ResC in EVERY full original parameter world, with one global original
mass budget. Finite carriers, zoom-cell multiplicities, final entry
floors, positive entry laws and all posterior caps are constructed here.
The only support lists supplied are the genuine full-block palettes and
fine-velocity-conditioned residual tables. -/
theorem original_residual_preparation {Λ I : Type*} {V : ℕ → Type*}
    [MeasurableSpace Λ] [MeasurableSpace I] [MeasurableSingletonClass I]
    [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)] [∀ i, Countable (V i)]
    (μ reference : Measure (Λ × ℝ)) [IsFiniteMeasure μ]
    (hμreference : μ ≤ reference) (E : Set (Λ × ℝ)) (hE : MeasurableSet E)
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (row : Λ × ℝ → Fin 2 → ℝ) (hrow : Measurable row)
    (b ρ Kold K : ℝ) (hb : 0 < b) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hKold : 1 ≤ Kold) (hK : 1 ≤ K)
    (ht : ∀ z∈E, z.2∈Icc (0 : ℝ) 1) (hcoeff : ∀ z∈E, ∀ j, |c z.1 j| ≤ Kold)
    (hrowBound : ∀ z∈E, ‖row z‖ ≤ K)
    (L : ℕ) (hL : 1 ≤ L) (s : ℕ → ℝ) (A ζ : ℝ) (hA : 1 ≤ A)
    (hs0 : s 0=1) (hs : ∀ i, 0 < s i)
    (hratio : ∀ i, i+1<L → s i ≤ A*s (i+1)) (hfloor : s (L-1) ≤ ζ)
    (hsmall : ∀ i<L, (2+3*(Kold+1))*b ≤ ρ*s i)
    (coarse : (Fin 7 → ℤ) → I)
    (blocks : (Fin 4 → ℤ) × I → Finset (Fin 7 → ℤ)) (P : ℕ)
    (hP : ∀ q, (blocks q).card ≤ P)
    (hblocks : ∀ z∈E, parameterCode ρ (c z.1) ∈
      blocks (originalFineState c b z,coarse (parameterCode ρ (c z.1))))
    (velocity : (i : ℕ) → Λ × ℝ → V i) (hv : ∀ i, Measurable (velocity i))
    (π : (i : ℕ) → Measure (V i)) [∀ i, IsProbabilityMeasure (π i)]
    (coarseV : (i : ℕ) → V i → I) (hcv : ∀ i, Measurable (coarseV i))
    (hcoarse : ∀ i<L, ∀ z∈E, coarseV i (velocity i z)=coarse (parameterCode ρ (c z.1)))
    (C : ℝ) (hC : 0 ≤ C) (cut M : ℕ → ℝ)
    (hcut : ∀ i<L, 0 < cut i) (hM : ∀ i<L, 0 ≤ M i)
    (hcap : ∀ i<L, ∀ w (B : Set (V i)), MeasurableSet B →
      reference {z | originalFineState c b z=w ∧ velocity i z∈B} ≤
        ENNReal.ofReal C * reference ((originalFineState c b) ⁻¹' {w}) * (π i) B)
    (table : (i : ℕ) → ((Fin 7 → ℤ) × (Fin 4 → ℤ)) × V i → Finset ℤ)
    (hcard : ∀ i<L, ∀ q, ((table i q).card : ℝ) ≤ M i)
    (hknown : ∀ i<L, ∀ z∈E,
      ⌊originalResidualValue (fun y => canonicalZoomCoefficients c ρ y.1) row Prod.snd z / s i⌋ ∈
        table i ((parameterCode ρ (c z.1),canonicalZoomCell c ρ (s i) z),velocity i z))
    (hosc : ∀ i<L, ∀ z∈E, ∀ z'∈E,
      originalFineState c b z=originalFineState c b z' →
      parameterCode ρ (c z.1)=parameterCode ρ (c z'.1) →
      |originalResidualValue (fun y => canonicalZoomCoefficients c ρ y.1) row Prod.snd z -
        originalResidualValue (fun y => canonicalZoomCoefficients c ρ y.1) row Prod.snd z'| ≤ s i) :
    ∃ S : Set (Λ × ℝ), MeasurableSet S ∧ S ⊆ E ∧
      μ E ≤ (∏ i∈Finset.range L,
        ((4 : ENNReal)^4*(⌈3*M i*(C/cut i)⌉₊+1 : ℕ))) * μ S +
          (∑ i : Fin L, ENNReal.ofReal (cut i.val)*(P*256 : ℕ))*reference univ ∧
      ∀ z∈S, ∀ z'∈S, parameterCode ρ (c z.1)=parameterCode ρ (c z'.1) →
        |originalResidualValue (fun y => canonicalZoomCoefficients c ρ y.1) row Prod.snd z -
          originalResidualValue (fun y => canonicalZoomCoefficients c ρ y.1) row Prod.snd z'| ≤
            2*(A+5*K^2)*(‖zpos (canonicalZoomCoefficients c ρ z.1) z.2-
              zpos (canonicalZoomCoefficients c ρ z'.1) z'.2‖+ζ) := by
  classical
  let world := fun z : Λ × ℝ => parameterCode ρ (c z.1)
  let cz := fun z : Λ × ℝ => canonicalZoomCoefficients c ρ z.1
  let entry := fun i : ℕ => originalZoomEntry c b ρ (s i)
  have hw : Measurable world := ((measurable_parameterCode ρ).comp hc).comp measurable_fst
  have hcz : Measurable cz := (measurable_canonicalZoomCoefficients hc ρ).comp measurable_fst
  have hstate := measurable_originalFineState hc b
  have he (i : ℕ) : Measurable (entry i) :=
    hstate.prodMk (hw.prodMk (measurable_canonicalZoomCell hc ρ (s i)))
  let pal : Fin L → I → ENNReal := fun i a => (π i.val) ((coarseV i.val) ⁻¹' {a})
  have hpal (i : Fin L) (F : Finset I) : ∑ a∈F, pal i a ≤ 1 := by
    change (∑ a∈F, (π i.val) ((coarseV i.val) ⁻¹' {a})) ≤ 1
    rw [sum_measure_preimage_singleton F (fun a _ => hcv i.val (measurableSet_singleton a))]
    exact (measure_mono (subset_univ _)).trans_eq (measure_univ : (π i.val) univ = 1)
  obtain ⟨R,hR,hRE,hloss,hentryFloor⟩ := original_zoom_entry_floors μ reference E hE c hc
    b ρ Kold hb hρ hρ1 hKold (fun i : Fin L => s i.val) (fun i => hs i.val)
    (fun i => hsmall i.val i.isLt) ht hcoeff coarse blocks P hP hblocks pal
    (fun i : Fin L => ENNReal.ofReal (cut i.val)) hpal
  let μ0 := μ.restrict R
  haveI : IsFiniteMeasure μ0 := by dsimp [μ0]; infer_instance
  let palettes := fun i (q : (Fin 7 → ℤ) × (Fin 4 → ℤ)) =>
    originalBinPalette (π i) ((coarseV i) ⁻¹' {coarse q.1})
  haveI : ∀ i q, IsProbabilityMeasure (palettes i q) := fun i q =>
    originalBinPalette_probability (π i) _
  have hentryPositive (i : ℕ) (hi : i<L) (z : Λ × ℝ) (hz : z∈R) :
      μ0 ((entry i) ⁻¹' {entry i z}) ≠ 0 :=
    ne_of_gt (lt_of_le_of_lt bot_le (hentryFloor ⟨i,hi⟩ z hz))
  have hentryCap (i : ℕ) (hi : i<L) (z : Λ × ℝ) (hz : z∈R)
      (B : Set (V i)) (hB : MeasurableSet B) :
      μ0 {y | entry i y=entry i z ∧ velocity i y∈B} ≤
        ENNReal.ofReal (C/cut i) * μ0 ((entry i) ⁻¹' {entry i z}) *
          (palettes i (originalResidualCell world cz Prod.snd (s i) z)) B := by
    have hh := original_refined_entry_posterior μ R hR (originalFineState c b) hstate
      world hw (canonicalZoomCell c ρ (s i)) (measurable_canonicalZoomCell hc ρ (s i))
      (velocity i) (hv i) (π i) (fun w => (coarseV i) ⁻¹' {coarse w})
      (fun w => hcv i (measurableSet_singleton _))
      (fun y hy => hcoarse i hi y (hRE hy))
      (fun w => reference ((originalFineState c b) ⁻¹' {w}))
      (ENNReal.ofReal C) (ENNReal.ofReal (cut i))
      (ENNReal.ofReal_pos.mpr (hcut i hi)).ne' ENNReal.ofReal_ne_top
      (fun w A hA => (hμreference _).trans (hcap i hi w A hA)) z hz
      (hentryFloor ⟨i,hi⟩ z hz) B hB
    have hent : entry i = originalRefinedEntry (originalFineState c b) world (canonicalZoomCell c ρ (s i)) := by
      funext y
      rfl
    rw [hent]
    simpa only [μ0,palettes,originalResidualCell,ENNReal.ofReal_div_of_pos (hcut i hi)] using hh
  have hfull : ∀ᵐ z ∂μ0, z∈R := ae_restrict_mem hR
  obtain ⟨S,hS,hSR,hmass,hcmp⟩ := original_world_residual_preparation μ0 world hw cz hcz row hrow
    Prod.snd measurable_snd R R hR hfull Subset.rfl K hK
    (fun z hz => ht z (hRE hz))
    (fun z _ i => (original_parameter_zoom_coefficients_bound ρ hρ (c z.1) i).trans hK)
    (fun z hz => hrowBound z (hRE hz)) L hL s A ζ hA hs0 hs hratio hfloor
    entry he velocity hv palettes (fun i => C/cut i) M
    (fun i hi => div_nonneg hC (hcut i hi).le) hM table hcard
    (fun i hi z hz => hknown i hi z (hRE hz))
    (by
      intro i hi z hz z' hz' heq
      exact congrArg Prod.snd heq)
    (by
      intro i hi z hz z' hz' heq
      exact hosc i hi z (hRE hz) z' (hRE hz') (congrArg Prod.fst heq)
        (congrArg (fun q : (Fin 4 → ℤ) × (Fin 7 → ℤ) × (Fin 4 → ℤ) => q.2.1) heq))
    hentryPositive hentryCap
  let D := ∏ i∈Finset.range L, ((4 : ENNReal)^4*(⌈3*M i*(C/cut i)⌉₊+1 : ℕ))
  have htotal : μ R ≤ D*μ S := by
    have hh := original_mass_of_worldwise_bounds μ0 world hw R S hR hS D hmass
    have heqR : μ0 R=μ R := Measure.restrict_eq_self μ (Subset.refl R)
    have heqS : μ0 S=μ S := Measure.restrict_eq_self μ hSR
    simpa only [heqR,heqS] using hh
  refine ⟨S,hS,hSR.trans hRE,?_,hcmp⟩
  calc
    μ E ≤ μ (R ∪ (E \ R)) := measure_mono (by
      intro z hz
      by_cases h : z∈R
      · exact Or.inl h
      · exact Or.inr ⟨hz,h⟩)
    _ ≤ μ R+μ (E \ R) := measure_union_le _ _
    _ ≤ _ := add_le_add htotal hloss

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
