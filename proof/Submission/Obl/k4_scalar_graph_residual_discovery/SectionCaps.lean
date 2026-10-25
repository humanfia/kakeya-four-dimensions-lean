/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file SectionCaps.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal

/-- Integrate the frozen fixed-time prior caps over the actual time window;
the original external palette factor may be included in `C`. -/
theorem product_mass_of_section_caps {X : Type*} [MeasurableSpace X]
    (θ : Measure X) [SFinite θ] {E : Set (X × ℝ)} (hE : MeasurableSet E)
    {I : Set ℝ} (hI : MeasurableSet I) (htime : ∀ p ∈ E, p.2 ∈ I)
    (C : ℝ≥0∞) (hcap : ∀ t ∈ I, θ {l | (l, t) ∈ E} ≤ C) :
    (θ.prod volume) E ≤ C * volume I := by
  have hpoint (t : ℝ) : θ {l | (l, t) ∈ E} ≤ I.indicator (fun _ => C) t := by
    by_cases ht : t ∈ I
    · rw [indicator_of_mem ht]
      exact hcap t ht
    · rw [indicator_of_notMem ht]
      have heq : {l | (l, t) ∈ E} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro l hl
        exact ht (htime (l, t) hl)
      rw [heq, measure_empty]
  rw [Measure.prod_apply_symm hE]
  calc
    _ ≤ ∫⁻ t, I.indicator (fun _ => C) t := lintegral_mono hpoint
    _ = _ := lintegral_indicator_const hI C

theorem incidence_mass_of_section_caps {X : Type*} [MeasurableSpace X]
    (θ : Measure X) [SFinite θ] (μ : Measure (X × ℝ))
    {U : ℝ≥0∞} (hμ : μ ≤ U • θ.prod volume)
    {E : Set (X × ℝ)} (hE : MeasurableSet E)
    {I : Set ℝ} (hI : MeasurableSet I) (htime : ∀ p ∈ E, p.2 ∈ I)
    (C : ℝ≥0∞) (hcap : ∀ t ∈ I, θ {l | (l, t) ∈ E} ≤ C) :
    μ E ≤ U * C * volume I := by
  calc
    _ ≤ (U • θ.prod volume) E := hμ _
    _ = U * (θ.prod volume) E := by rw [Measure.smul_apply]; rfl
    _ ≤ U * (C * volume I) := mul_le_mul_of_nonneg_left
      (product_mass_of_section_caps θ hE hI htime C hcap) zero_le
    _ = _ := (mul_assoc _ _ _).symm

end Submission.Obl.k4_scalar_graph_residual_discovery
