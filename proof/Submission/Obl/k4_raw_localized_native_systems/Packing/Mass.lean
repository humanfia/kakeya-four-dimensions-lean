/- Adapted from this LOT tree, o197, session x0690, Packing/Mass.lean,
   branch snapshot 9f1b6476; preserving original attributions below. -/
import Submission.Obl.k4_remainder_pure_profile_normalization.Overlap

namespace Submission.Obl.k4_raw_localized_native_systems.Packing

open MeasureTheory Set

noncomputable section

/-- Full witness masses are packed using the original observation-list overlap
and one common base window. The number of witnesses never enters the estimate. -/
theorem full_mass_le_base_volume {Ω Y I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y] [Fintype I]
    (μ : Measure Ω) (ν : Measure Y) (base : Ω → Y) (hbase : Measurable base)
    (F : I → Set Ω) (hF : ∀ i, MeasurableSet (F i))
    (lst : Ω → Finset I) (K c : ENNReal)
    (hmem : ∀ i q, q ∈ F i → i ∈ lst q)
    (hcard : ∀ q, ((lst q).card : ENNReal) ≤ K)
    (hcap : Measure.map base μ ≤ c • ν)
    (Z : Set Y) (hZ : MeasurableSet Z) (hFZ : ∀ i, F i ⊆ base ⁻¹' Z) :
    (∑ i, μ (F i)) ≤ K * c * ν Z := by
  have hpre : MeasurableSet (base ⁻¹' Z) := hZ.preimage hbase
  calc
    (∑ i, μ (F i)) = ∑ i, μ.restrict (F i) (base ⁻¹' Z) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Measure.restrict_apply hpre, inter_eq_right.mpr (hFZ i)]
    _ ≤ K * μ (base ⁻¹' Z) :=
      k4_remainder_pure_profile_normalization.sum_restrict_apply_le_of_lists
        μ F hF lst K hmem hcard _ hpre
    _ = K * Measure.map base μ Z := by rw [Measure.map_apply hbase hZ]
    _ ≤ K * (c • ν) Z := mul_le_mul' le_rfl (hcap Z)
    _ = _ := by rw [Measure.smul_apply, smul_eq_mul]; ring

/-- Pushforward to the original graph coordinates keeps all witness masses,
so the same packing inequality applies to the raw laws in `RawSupport`. -/
theorem full_graph_mass_le_base_volume {Ω Y X I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSpace X] [Fintype I]
    (μ : Measure Ω) (ν : Measure Y) (base : Ω → Y) (hbase : Measurable base)
    (graph : Ω → X) (hgraph : Measurable graph)
    (F : I → Set Ω) (hF : ∀ i, MeasurableSet (F i))
    (lst : Ω → Finset I) (K c : ENNReal)
    (hmem : ∀ i q, q ∈ F i → i ∈ lst q)
    (hcard : ∀ q, ((lst q).card : ENNReal) ≤ K)
    (hcap : Measure.map base μ ≤ c • ν)
    (Z : Set Y) (hZ : MeasurableSet Z) (hFZ : ∀ i, F i ⊆ base ⁻¹' Z) :
    (∑ i, Measure.map graph (μ.restrict (F i)) univ) ≤ K * c * ν Z := by
  simpa only [Measure.map_apply hgraph MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ] using
    full_mass_le_base_volume μ ν base hbase F hF lst K c hmem hcard hcap Z hZ hFZ

end
end Submission.Obl.k4_raw_localized_native_systems.Packing
