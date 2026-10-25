-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.NativeStripStates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/NativeStripStates.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/NativeStripStates.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/NativeStripStates.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.NativeStripVisits
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalSupportPriors


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

/-- Both the coarse physical cube and its normal strip are functions
of ONE original fine physical state. -/
def nativeStripState (b ρ p : ℝ) (row : (Fin 4 → ℤ) → Fin 3 → ℝ)
    (q : Fin 4 → ℤ) : (Fin 4 → ℤ) × ℤ :=
  let C : Fin 4 → ℤ := fun j => ⌊b * (q j : ℝ) / ρ⌋
  (C, ⌊(b * (q 3 : ℝ) - ∑ j, row C j * (b * (q j.castSucc : ℝ))) / p⌋)

theorem measurable_nativeStripState (b ρ p : ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) : Measurable (nativeStripState b ρ p row) :=
  measurable_of_countable _

theorem nativeStripState_original (b ρ p : ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ)
    (signal : Polynomial ℝ) (a v : Fin 3 → ℝ) (t : ℝ) :
    nativeStripState b ρ p row
      (fun j => ⌊originalPhysicalCoordinates signal a v t j / b⌋) =
      (roundedPhysicalCode b ρ (originalPhysicalCoordinates signal a v t),
        ⌊originalNormalStateCenter signal a v
          (row (roundedPhysicalCode b ρ (originalPhysicalCoordinates signal a v t))) b t / p⌋) := by
  have hlast : originalPhysicalCoordinates signal a v t 3 = signal.eval t := by
    change (Fin.snoc (fun j : Fin 3 => a j + v j * t) (signal.eval t) : Fin 4 → ℝ)
      (Fin.last 3) = _
    exact Fin.snoc_last _ _
  have hbase (j : Fin 3) : originalPhysicalCoordinates signal a v t j.castSucc =
      a j + v j * t := Fin.snoc_castSucc _ _ j
  apply Prod.ext
  · rfl
  · change ⌊(b * (⌊originalPhysicalCoordinates signal a v t 3 / b⌋ : ℝ) -
        ∑ j, row (roundedPhysicalCode b ρ (originalPhysicalCoordinates signal a v t)) j *
          (b * (⌊originalPhysicalCoordinates signal a v t j.castSucc / b⌋ : ℝ))) / p⌋ = _
    simp only [hlast, hbase, originalNormalStateCenter, mul_comm]

def originalStripLabel {X : Type*} (b ρ p : ℝ)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (signal : X → Polynomial ℝ)
    (a v : X → Fin 3 → ℝ) (z : X × ℝ) : (Fin 4 → ℤ) × ℤ :=
  nativeStripState b ρ p row
    (fun j => ⌊originalPhysicalCoordinates (signal z.1) (a z.1) (v z.1) z.2 j / b⌋)

theorem measurable_originalStripLabel {X : Type*} [MeasurableSpace X]
    (b ρ p : ℝ) (row : (Fin 4 → ℤ) → Fin 3 → ℝ)
    (signal : X → Polynomial ℝ) (a v : X → Fin 3 → ℝ)
    (hphys : Measurable (fun z : X × ℝ =>
      originalPhysicalCoordinates (signal z.1) (a z.1) (v z.1) z.2)) :
    Measurable (originalStripLabel b ρ p row signal a v) := by
  apply (measurable_nativeStripState b ρ p row).comp
  change Measurable (fun z : X × ℝ => fun j : Fin 4 =>
    (⌊originalPhysicalCoordinates (signal z.1) (a z.1) (v z.1) z.2 j / b⌋ : ℤ))
  fun_prop

def originalStripDensity {Ω : Type*} (E : Set Ω) (label : Ω → (Fin 4 → ℤ) × ℤ)
    (i : (Fin 4 → ℤ) × ℤ) : Ω → ENNReal :=
  (E ∩ label ⁻¹' {i}).indicator (fun _ => 1)

theorem measurable_originalStripDensity {Ω : Type*} [MeasurableSpace Ω]
    {E : Set Ω} (hE : MeasurableSet E)
    (label : Ω → (Fin 4 → ℤ) × ℤ) (hlabel : Measurable label)
    (i : (Fin 4 → ℤ) × ℤ) : Measurable (originalStripDensity E label i) :=
  measurable_const.indicator (hE.inter (hlabel (measurableSet_singleton i)))

theorem originalStripDensity_ne_zero {Ω : Type*} (E : Set Ω)
    (label : Ω → (Fin 4 → ℤ) × ℤ) (i : (Fin 4 → ℤ) × ℤ) (x : Ω) :
    originalStripDensity E label i x ≠ 0 ↔ x ∈ E ∧ label x = i := by
  classical
  simp [originalStripDensity]

theorem withDensity_originalStripDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {E : Set Ω} (hE : MeasurableSet E)
    (label : Ω → (Fin 4 → ℤ) × ℤ) (hlabel : Measurable label)
    (i : (Fin 4 → ℤ) × ℤ) :
    μ.withDensity (originalStripDensity E label i) = μ.restrict (E ∩ label ⁻¹' {i}) := by
  rw [originalStripDensity, withDensity_indicator (hE.inter (hlabel (measurableSet_singleton i)))]
  change (μ.restrict (E ∩ label ⁻¹' {i})).withDensity 1 = _
  exact withDensity_one

/-- A later strip restriction is still dominated by the original
product law on the original active strip. -/
theorem original_strip_submeasure_domination {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    (ν : Measure X) (τ : Measure T) (μ : Measure (X × T)) (K : ENNReal)
    {E : Set (X × T)} (hE : MeasurableSet E)
    (label : X × T → (Fin 4 → ℤ) × ℤ) (hlabel : Measurable label)
    (hdom : μ ≤ K • ν.prod τ) (hfull : ∀ᵐ z ∂μ, z ∈ E)
    (i : (Fin 4 → ℤ) × ℤ) :
    μ.restrict (label ⁻¹' {i}) ≤ K • (ν.prod τ).withDensity (originalStripDensity E label i) := by
  have hμ : μ.restrict E = μ := Measure.restrict_eq_self_of_ae_mem hfull
  have hi := hlabel (measurableSet_singleton i)
  calc
    _ = (μ.restrict E).restrict (label ⁻¹' {i}) := by rw [hμ]
    _ ≤ ((K • ν.prod τ).restrict E).restrict (label ⁻¹' {i}) :=
      Measure.restrict_mono le_rfl (Measure.restrict_mono le_rfl hdom)
    _ = _ := by
      rw [withDensity_originalStripDensity (ν.prod τ) hE label hlabel i,
        Measure.restrict_smul, Measure.restrict_smul, Measure.restrict_restrict hi]
      rw [inter_comm]

/-- The supporting trajectory prior is fixed by the original active
strip, before a later incidence submeasure or whole-group choice. -/
theorem ae_original_strip_support {X T : Type*}
    [MeasurableSpace X] [MeasurableSpace T]
    (ν : Measure X) [SFinite ν] (τ : Measure T) [SFinite τ]
    (μ : Measure (X × T)) (K : ENNReal) {E : Set (X × T)} (hE : MeasurableSet E)
    (label : X × T → (Fin 4 → ℤ) × ℤ) (hlabel : Measurable label)
    (hdom : μ ≤ K • ν.prod τ) (hfull : ∀ᵐ z ∂μ, z ∈ E)
    (i : (Fin 4 → ℤ) × ℤ) :
    ∀ᵐ z ∂μ.restrict (label ⁻¹' {i}),
      z.1 ∈ originalOccupationSupport τ (originalStripDensity E label i) :=
  ae_original_occupation_support ν τ (measurable_originalStripDensity hE label hlabel i) _ K
    (original_strip_submeasure_domination ν τ μ K hE label hlabel hdom hfull i)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
