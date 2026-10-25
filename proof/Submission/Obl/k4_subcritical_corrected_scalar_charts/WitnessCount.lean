/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/WitnessCount.lean`. Original attributions are retained below. -/
/- Adapted from this LOT tree, o218, session x0760, commit 1cac570d6b7e29a2b2bcfee7642734d13baeb474,
   `Submission/Obl/k4_horizontal_endpoint_wide_return/WitnessCount.lean`. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.WitnessInheritance

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open MeasureTheory Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- Count full original witnesses even when their only overlaps are null.
The floor belongs to each original witness, not to a later chart restriction. -/
theorem original_witness_count {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : ι → Set Ω) (S : Finset ι) (G : Set Ω)
    (hW : ∀ i ∈ S, MeasurableSet (W i))
    (hunique : ∀ᵐ z ∂μ, ∀ i ∈ S, ∀ j ∈ S, z ∈ W i → z ∈ W j → i = j)
    (hG : ∀ i ∈ S, W i ⊆ G) {m C : ℝ} (hm : 0 < m) (hC : 0 ≤ C)
    (hfloor : ∀ i ∈ S, ENNReal.ofReal m ≤ μ (W i))
    (hcap : μ G ≤ ENNReal.ofReal C) : (S.card : ℝ) ≤ C / m := by
  have hd : (S : Set ι).Pairwise (fun i j => AEDisjoint μ (W i) (W j)) := by
    intro i hi j hj hij
    have hnot : ∀ᵐ z ∂μ, z ∉ W i ∩ W j := by
      filter_upwards [hunique] with z hz
      exact fun hmem => hij (hz i hi j hj hmem.1 hmem.2)
    simpa only [AEDisjoint, ae_iff, not_not, Set.ofPred_mem_eq] using hnot
  have hb : (S.card : ENNReal) * ENNReal.ofReal m ≤ ENNReal.ofReal C := by
    calc
      _ = ∑ _i ∈ S, ENNReal.ofReal m := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ S, μ (W i) := Finset.sum_le_sum fun i hi => hfloor i hi
      _ = μ (⋃ i ∈ S, W i) :=
        (measure_biUnion_finset₀ hd fun i hi => (hW i hi).nullMeasurableSet).symm
      _ ≤ μ G := measure_mono (iUnion₂_subset fun i hi => hG i hi)
      _ ≤ ENNReal.ofReal C := hcap
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hm.le, ENNReal.toReal_ofReal hC] at hr
  exact (le_div_iff₀ hm).mpr hr

/-- Original witnesses may enter the counting box almost everywhere. Their
full original floors still count; no later slice replaces a witness. -/
theorem original_witness_count_ae {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : ι → Set Ω) (S : Finset ι) (G : Set Ω)
    (hW : ∀ i ∈ S, MeasurableSet (W i))
    (hunique : ∀ᵐ z ∂μ, ∀ i ∈ S, ∀ j ∈ S, z ∈ W i → z ∈ W j → i = j)
    (hG : ∀ᵐ z ∂μ, ∀ i ∈ S, z ∈ W i → z ∈ G) {m C : ℝ} (hm : 0 < m) (hC : 0 ≤ C)
    (hfloor : ∀ i ∈ S, ENNReal.ofReal m ≤ μ (W i))
    (hcap : μ G ≤ ENNReal.ofReal C) : (S.card : ℝ) ≤ C / m := by
  apply original_witness_count μ W S (⋃ i ∈ S, W i) hW hunique
    (fun i hi => subset_iUnion₂_of_subset i hi subset_rfl) hm hC hfloor
  refine (measure_mono_ae ?_).trans hcap
  filter_upwards [hG] with z hz
  intro hmem
  obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hmem
  exact hz i hi hzi

/-- Same-depth native labels may occupy different closed dyadic blocks.
Their original witnesses still have multiplicity one almost everywhere. -/
theorem native_original_witness_count {α ι : Type*}
    [MeasurableSpace α] [Countable ι]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure (α × ℝ)) (c : ENNReal)
    (hdom : μ ≤ c • (ν.prod volume)) (T : ℕ) (j : ι → Fin (2 ^ T)) (A : ι → Set α)
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i'))
    (W : ι → Set (α × ℝ)) (S : Finset ι) (G : Set (α × ℝ))
    (hW : ∀ i ∈ S, MeasurableSet (W i))
    (hsub : ∀ i ∈ S, W i ⊆ A i ×ˢ I T (j i))
    (hG : ∀ i ∈ S, W i ⊆ G) {m C : ℝ} (hm : 0 < m) (hC : 0 ≤ C)
    (hfloor : ∀ i ∈ S, ENNReal.ofReal m ≤ μ (W i))
    (hcap : μ G ≤ ENNReal.ofReal C) : (S.card : ℝ) ≤ C / m := by
  apply original_witness_count μ W S G hW ?_ hG hm hC hfloor hcap
  filter_upwards [true_assignments_ae_unique ν μ c hdom T j A hdisj] with z hz
  intro i hi i' hi' hzi hzi'
  obtain ⟨hAi, hIi⟩ := hsub i hi hzi
  obtain ⟨hAi', hIi'⟩ := hsub i' hi' hzi'
  exact hz i i' hAi hIi hAi' hIi'

end Submission.Obl.k4_subcritical_corrected_scalar_charts
