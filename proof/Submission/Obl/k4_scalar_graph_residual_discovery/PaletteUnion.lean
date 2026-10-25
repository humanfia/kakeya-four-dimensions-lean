/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file PaletteUnion.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ResidualRenewal

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory

/-- Any union of complete fine states inherits the same relative palette
ceiling, with its own current mass as denominator. -/
theorem whole_state_union_palette_cap {X Q V : Type*}
    [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    [MeasurableSpace V]
    (μ : Measure X) (state : X → Q) (hstate : Measurable state)
    (code : X → V) (hcode : Measurable code) (π : Measure V) (C : ENNReal)
    (hcap : ∀ q (A : Set V), MeasurableSet A →
      μ {p | state p = q ∧ code p ∈ A} ≤ C * μ (state ⁻¹' {q}) * π A)
    (S : Set Q) (A : Set V) (hA : MeasurableSet A) :
    μ {p | state p ∈ S ∧ code p ∈ A} ≤ C * μ (state ⁻¹' S) * π A := by
  classical
  let E : Set X := {p | state p ∈ S ∧ code p ∈ A}
  have hS : MeasurableSet (state ⁻¹' S) := hstate (Set.to_countable S).measurableSet
  have hE : MeasurableSet E := hS.inter (hcode hA)
  have hpiece (q : Q) : μ (E ∩ state ⁻¹' {q}) ≤
      C * μ ((state ⁻¹' S) ∩ state ⁻¹' {q}) * π A := by
    by_cases hq : q ∈ S
    · have hinc : state ⁻¹' {q} ⊆ state ⁻¹' S := by
        intro p hp
        change state p ∈ S
        simpa only [mem_singleton_iff.mp hp] using hq
      have heq : E ∩ state ⁻¹' {q} = {p | state p = q ∧ code p ∈ A} := by
        ext p
        constructor
        · rintro ⟨⟨_, hv⟩, hpq⟩
          exact ⟨hpq, hv⟩
        · rintro ⟨hpq, hv⟩
          exact ⟨⟨by simpa only [hpq] using hq, hv⟩, hpq⟩
      rw [heq, inter_eq_right.mpr hinc]
      exact hcap q A hA
    · have hz : (state ⁻¹' S) ∩ state ⁻¹' {q} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro p ⟨hp, hpq⟩
        exact hq (by simpa only [mem_preimage, mem_singleton_iff.mp hpq] using hp)
      calc
        _ ≤ μ ((state ⁻¹' S) ∩ state ⁻¹' {q}) := measure_mono (fun _ hp => ⟨hp.1.1, hp.2⟩)
        _ = 0 := by rw [hz, measure_empty]
        _ ≤ _ := zero_le
  rw [Submission.Obl.k4_crop_angular_finite_tail.measure_eq_tsum_label μ hstate hE,
    Submission.Obl.k4_crop_angular_finite_tail.measure_eq_tsum_label μ hstate hS]
  calc
    _ ≤ ∑' q, C * μ ((state ⁻¹' S) ∩ state ⁻¹' {q}) * π A :=
      ENNReal.tsum_le_tsum hpiece
    _ = _ := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]

end Submission.Obl.k4_scalar_graph_residual_discovery
