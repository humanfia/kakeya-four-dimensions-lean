import Submission.Obl.k4_general_wide_layer_offset_comparison.WeightedComparisonDecay

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/AEComparison.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Metric
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

noncomputable section

/-- The literal smoothed pair law, with its original almost-everywhere
support conditions. These conditions can be made pointwise on a conull
measurable subtype without any disintegration assumption. -/
structure AEWeightComparison (ι₁ ι₂ Λ Ω : Type*) [MeasurableSpace Ω] where
  law : Measure Ω
  lab₁ : ι₁ → Λ
  lab₂ : ι₂ → Λ
  φ₁ : ι₁ → EuclideanSpace ℂ (Fin 3) → ℂ
  φ₂ : ι₂ → EuclideanSpace ℂ (Fin 3) → ℂ
  src : Ω → ι₁
  wit : Ω → ι₂
  point : Ω → EuclideanSpace ℝ (Fin 3)
  value : Ω → ℝ
  error : ℝ
  K : ℝ
  weight₁ : Λ → ℝ
  weight₂ : Λ → ℝ
  finite : IsFiniteMeasure law
  sheet₁ : ∀ i, IsMatchSheet (φ₁ i)
  sheet₂ : ∀ i, IsMatchSheet (φ₂ i)
  src_meas : ∀ i, MeasurableSet {p | src p = i}
  wit_meas : ∀ i, MeasurableSet {p | wit p = i}
  point_meas : Measurable point
  lab_eq : ∀ᵐ p ∂law, lab₁ (src p) = lab₂ (wit p)
  point_mem : ∀ᵐ p ∂law, ‖point p‖ ≤ 1 / 2
  error_pos : 0 < error
  near_src : ∀ᵐ p ∂law, ‖φ₁ (src p) (emb (point p)) - (value p : ℂ)‖ ≤ error
  near_wit : ∀ᵐ p ∂law, ‖φ₂ (wit p) (emb (point p)) - (value p : ℂ)‖ ≤ error
  K_nonneg : 0 ≤ K
  weight₁_nonneg : ∀ l, 0 ≤ weight₁ l
  weight₂_nonneg : ∀ l, 0 ≤ weight₂ l
  density_src : ∀ i (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
    law {p | src p = i ∧ point p ∈ U} ≤
      ENNReal.ofReal (K * weight₁ (lab₁ i)) * volume U
  density_wit : ∀ i (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
    law {p | wit p = i ∧ point p ∈ U} ≤
      ENNReal.ofReal (K * weight₂ (lab₂ i)) * volume U

namespace AEWeightComparison

variable {ι₁ ι₂ Λ Ω : Type*} [MeasurableSpace Ω]
    (S : AEWeightComparison ι₁ ι₂ Λ Ω)

def Good (p : Ω) : Prop :=
  S.lab₁ (S.src p) = S.lab₂ (S.wit p) ∧ ‖S.point p‖ ≤ 1 / 2 ∧
    ‖S.φ₁ (S.src p) (emb (S.point p)) - (S.value p : ℂ)‖ ≤ S.error ∧
    ‖S.φ₂ (S.wit p) (emb (S.point p)) - (S.value p : ℂ)‖ ≤ S.error

theorem exists_full_carrier :
    ∃ G : Set Ω, MeasurableSet G ∧ S.law Gᶜ = 0 ∧ ∀ p ∈ G, S.Good p := by
  have hae : ∀ᵐ p ∂S.law, S.Good p := by
    filter_upwards [S.lab_eq, S.point_mem, S.near_src, S.near_wit] with p hl hp hs hw
    exact ⟨hl, hp, hs, hw⟩
  rw [ae_iff] at hae
  obtain ⟨B, hsub, hB, hnull⟩ := exists_measurable_superset_of_null hae
  refine ⟨Bᶜ, hB.compl, by simpa using hnull, ?_⟩
  intro p hp
  by_contra hn
  exact hp (hsub hn)

/-- Restrict only the ambient type, retaining all original measure units. -/
def onCarrier (G : Set Ω) (hG : MeasurableSet G) (hgood : ∀ p ∈ G, S.Good p) :
    TwoWeightComparison ι₁ ι₂ Λ G := by
  letI := S.finite
  refine
    { law := S.law.comap (Subtype.val : G → Ω)
      lab₁ := S.lab₁
      lab₂ := S.lab₂
      φ₁ := S.φ₁
      φ₂ := S.φ₂
      src := fun p => S.src p.val
      wit := fun p => S.wit p.val
      point := fun p => S.point p.val
      value := fun p => S.value p.val
      error := S.error
      K := S.K
      weight₁ := S.weight₁
      weight₂ := S.weight₂
      finite := ?_
      sheet₁ := S.sheet₁
      sheet₂ := S.sheet₂
      src_meas := fun i => (S.src_meas i).preimage measurable_subtype_coe
      wit_meas := fun i => (S.wit_meas i).preimage measurable_subtype_coe
      point_meas := S.point_meas.comp measurable_subtype_coe
      lab_eq := fun p => (hgood p.val p.property).1
      point_mem := fun p => (hgood p.val p.property).2.1
      error_pos := S.error_pos
      near_src := fun p => (hgood p.val p.property).2.2.1
      near_wit := fun p => (hgood p.val p.property).2.2.2
      K_nonneg := S.K_nonneg
      weight₁_nonneg := S.weight₁_nonneg
      weight₂_nonneg := S.weight₂_nonneg
      density_src := ?_
      density_wit := ?_ }
  · constructor
    rw [comap_subtype_coe_apply hG]
    exact (measure_mono (subset_univ _)).trans_lt (measure_lt_top S.law univ)
  · intro i U hU
    rw [comap_subtype_coe_apply hG]
    apply (measure_mono ?_).trans (S.density_src i U hU)
    rintro p ⟨q, hq, rfl⟩
    exact hq
  · intro i U hU
    rw [comap_subtype_coe_apply hG]
    apply (measure_mono ?_).trans (S.density_wit i U hU)
    rintro p ⟨q, hq, rfl⟩
    exact hq

/-- Every original event has exactly its original mass on a full carrier. -/
theorem carrier_event_measure (G : Set Ω) (hG : MeasurableSet G)
    (hfull : S.law Gᶜ = 0) (E : Set Ω) :
    (S.law.comap (Subtype.val : G → Ω)) (Subtype.val ⁻¹' E) = S.law E := by
  rw [comap_subtype_coe_apply hG, image_preimage_eq_inter_range, Subtype.range_coe]
  apply measure_congr
  have hmem : ∀ᵐ p ∂S.law, p ∈ G := by rw [ae_iff]; exact hfull
  filter_upwards [hmem] with p hp
  simp only [mem_inter_iff, hp, and_true]

end AEWeightComparison
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
