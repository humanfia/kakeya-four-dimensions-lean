/- Adapted from this LOT tree, o091, session x0299, commit 918e44e,
Submission/Obl/k4_dyadic_crop_typicality/Transfer.lean. -/

import Mathlib

/-!
# Abstract density transfer

Densities of observation laws with respect to a product `m × count` with a countable label set:
* `lintegral_prod_count`: an integral over `m × count` is the sum of its label slices;
* `sum_lower_ratio_le`: restricted laws concentrated on boundedly overlapping sets have
  densities below `δ` times the full density only on total mass `K δ`;
* `map_pair_const_label`: a law whose label is almost surely constant.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace Submission.Obl.k4_crop_base_finite_tail

section Slices

variable {Y ι : Type*} [MeasurableSpace Y] [MeasurableSpace ι] [Countable ι]
  [MeasurableSingletonClass ι]

lemma lintegral_prod_count (m : Measure Y) [SFinite m] {f : Y × ι → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ z, f z ∂(m.prod Measure.count) = ∑' i, ∫⁻ y, f (y, i) ∂m := by
  rw [lintegral_prod_symm _ hf.aemeasurable, lintegral_count]

lemma setLIntegral_prod_count (m : Measure Y) [SFinite m] {f : Y × ι → ℝ≥0∞}
    (hf : Measurable f) {U : Set (Y × ι)} (hU : MeasurableSet U) :
    ∫⁻ z in U, f z ∂(m.prod Measure.count) =
      ∑' i, ∫⁻ y in {y | (y, i) ∈ U}, f (y, i) ∂m := by
  rw [← lintegral_indicator hU, lintegral_prod_count m (hf.indicator hU)]
  congr 1
  funext i
  have hUi : MeasurableSet {y : Y | (y, i) ∈ U} := measurable_prodMk_right hU
  rw [← lintegral_indicator hUi]
  congr 1

lemma withDensity_prod_singleton (m : Measure Y) [SFinite m] {D : Y × ι → ℝ≥0∞}
    (hD : Measurable D) {U : Set Y} (hU : MeasurableSet U) (i : ι) :
    ((m.prod Measure.count).withDensity D) (U ×ˢ {i}) = ∫⁻ y in U, D (y, i) ∂m := by
  rw [withDensity_apply _ (hU.prod (measurableSet_singleton i)),
    setLIntegral_prod_count m hD (hU.prod (measurableSet_singleton i))]
  rw [tsum_eq_single i]
  · congr 2
    ext y
    simp
  · intro j hj
    have : {y | (y, j) ∈ U ×ˢ ({i} : Set ι)} = ∅ := by
      ext y
      simp [hj]
    rw [this, Measure.restrict_empty, lintegral_zero_measure]

end Slices

section Coarsening

variable {X Y ι κ : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι]
  [MeasurableSpace κ] [Countable κ] [MeasurableSingletonClass κ]

/-- A law whose label is almost surely `i₀`. -/
theorem map_pair_const_label (m : Measure Y) [SFinite m] {μ : Measure X}
    {ψ : X → Y} (hψ : Measurable ψ) {s : X → ι} (i₀ : ι)
    (hconst : ∀ᵐ x ∂μ, s x = i₀) {H : Y → ℝ≥0∞} (hH : Measurable H)
    (hlaw : μ.map ψ = m.withDensity H) :
    μ.map (fun x => (ψ x, s x)) =
      (m.prod Measure.count).withDensity ({z | z.2 = i₀}.indicator (fun z => H z.1)) := by
  have hmeas : Measurable ({z : Y × ι | z.2 = i₀}.indicator (fun z => H z.1)) :=
    (hH.comp measurable_fst).indicator (measurable_snd (measurableSet_singleton i₀))
  have hcongr : μ.map (fun x => (ψ x, s x)) = μ.map (fun x => (ψ x, i₀)) := by
    apply Measure.map_congr
    filter_upwards [hconst] with x hx
    rw [hx]
  rw [hcongr]
  ext U hU
  rw [Measure.map_apply (hψ.prodMk measurable_const) hU, withDensity_apply _ hU,
    setLIntegral_prod_count m hmeas hU, tsum_eq_single i₀]
  · have : (fun x => (ψ x, i₀)) ⁻¹' U = ψ ⁻¹' {y | (y, i₀) ∈ U} := rfl
    have hUi : MeasurableSet {y : Y | (y, i₀) ∈ U} := measurable_prodMk_right hU
    rw [this, ← Measure.map_apply hψ hUi, hlaw, withDensity_apply _ hUi]
    congr 1
    funext y
    simp [Set.indicator]
  · intro j hj
    have : ∀ y, ({z : Y × ι | z.2 = i₀}.indicator (fun z => H z.1)) (y, j) = 0 := by
      intro y
      simp [Set.indicator, hj]
    simp [this]

end Coarsening

section Overlap

variable {X Z Γ : Type*} [MeasurableSpace X] [MeasurableSpace Z] [Fintype Γ]

/-- Restricted laws concentrated on sets of bounded overlap `K` have densities below `δ` times the
full density only on total original mass `K δ`. -/
theorem sum_lower_ratio_le (ref : Measure Z) (μ : Measure X)
    {Φ : X → Z} (hΦ : Measurable Φ) {G : Z → ℝ≥0∞} (hG : Measurable G)
    (hlaw : μ.map Φ = ref.withDensity G)
    (S : Γ → Set X)
    (D : Γ → Z → ℝ≥0∞) (hD : ∀ γ, Measurable (D γ))
    (hlawγ : ∀ γ, (μ.restrict (S γ)).map Φ = ref.withDensity (D γ))
    (C : Γ → Set Z) (hC : ∀ γ, MeasurableSet (C γ))
    (hsupp : ∀ γ, ∀ᵐ x ∂(μ.restrict (S γ)), Φ x ∈ C γ)
    (K : ℝ≥0∞) (hK : ∀ z, ∑ γ, (C γ).indicator (fun _ => (1 : ℝ≥0∞)) z ≤ K) (δ : ℝ≥0∞) :
    ∑ γ, μ (S γ ∩ {x | D γ (Φ x) < δ * G (Φ x)}) ≤ K * δ * μ univ := by
  have hB : ∀ γ, MeasurableSet {z | D γ z < δ * G z} := fun γ =>
    measurableSet_lt (hD γ) (measurable_const.mul hG)
  have hterm : ∀ γ, μ (S γ ∩ {x | D γ (Φ x) < δ * G (Φ x)}) ≤
      ∫⁻ z, δ * (C γ).indicator G z ∂ref := by
    intro γ
    have hzero : (ref.withDensity (D γ)) (C γ)ᶜ = 0 := by
      rw [← hlawγ γ, Measure.map_apply hΦ (hC γ).compl]
      exact ae_iff.1 (hsupp γ)
    calc μ (S γ ∩ {x | D γ (Φ x) < δ * G (Φ x)})
        = (ref.withDensity (D γ)) {z | D γ z < δ * G z} := by
          rw [← hlawγ γ, Measure.map_apply hΦ (hB γ), Measure.restrict_apply (hΦ (hB γ)),
            inter_comm]
          rfl
      _ ≤ (ref.withDensity (D γ)) ({z | D γ z < δ * G z} ∩ C γ) +
            (ref.withDensity (D γ)) (C γ)ᶜ := by
          calc (ref.withDensity (D γ)) {z | D γ z < δ * G z}
              ≤ (ref.withDensity (D γ)) (({z | D γ z < δ * G z} ∩ C γ) ∪ (C γ)ᶜ) := by
                apply measure_mono
                intro z hz
                by_cases hzC : z ∈ C γ
                · exact Or.inl ⟨hz, hzC⟩
                · exact Or.inr hzC
            _ ≤ _ := measure_union_le _ _
      _ = ∫⁻ z in {z | D γ z < δ * G z} ∩ C γ, D γ z ∂ref := by
          rw [hzero, add_zero, withDensity_apply _ ((hB γ).inter (hC γ))]
      _ ≤ ∫⁻ z in {z | D γ z < δ * G z} ∩ C γ, δ * G z ∂ref := by
          apply setLIntegral_mono (measurable_const.mul hG)
          intro z hz
          exact hz.1.le
      _ ≤ ∫⁻ z in C γ, δ * G z ∂ref := lintegral_mono_set inter_subset_right
      _ = ∫⁻ z, δ * (C γ).indicator G z ∂ref := by
          rw [← lintegral_indicator (hC γ)]
          congr 1
          funext z
          by_cases hz : z ∈ C γ <;> simp [Set.indicator, hz]
  calc ∑ γ, μ (S γ ∩ {x | D γ (Φ x) < δ * G (Φ x)})
      ≤ ∑ γ, ∫⁻ z, δ * (C γ).indicator G z ∂ref := Finset.sum_le_sum fun γ _ => hterm γ
    _ = ∫⁻ z, ∑ γ, δ * (C γ).indicator G z ∂ref := by
        rw [lintegral_finsetSum]
        intro γ _
        exact measurable_const.mul (hG.indicator (hC γ))
    _ ≤ ∫⁻ z, δ * (K * G z) ∂ref := by
        apply lintegral_mono
        intro z
        simp only
        rw [← Finset.mul_sum]
        gcongr
        calc ∑ γ, (C γ).indicator G z
            = (∑ γ, (C γ).indicator (fun _ => (1 : ℝ≥0∞)) z) * G z := by
              rw [Finset.sum_mul]
              congr 1
              funext γ
              by_cases hz : z ∈ C γ <;> simp [Set.indicator, hz]
          _ ≤ K * G z := by gcongr; exact hK z
    _ = K * δ * μ univ := by
        have e1 : (fun z => δ * (K * G z)) = fun z => (δ * K) * G z := by
          funext z
          ring
        rw [e1, lintegral_const_mul _ hG]
        have h1 : ∫⁻ z, G z ∂ref = μ univ := by
          rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, ← hlaw,
            Measure.map_apply hΦ MeasurableSet.univ, preimage_univ]
        rw [h1]
        ring

end Overlap

end Submission.Obl.k4_crop_base_finite_tail
