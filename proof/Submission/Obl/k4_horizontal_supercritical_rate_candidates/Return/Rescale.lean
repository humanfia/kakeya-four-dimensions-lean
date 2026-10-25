import Mathlib

/-!
# Rescaling time on one dyadic block

An incidence law dominated by `K • ν ⊗ dt` and carried by `A × [t₀, t₀ + q]` becomes,
after the time change `τ = (t - t₀) / q`, dominated by `K q • ν|_A ⊗ dτ`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The block time change. -/
def rescale {α : Type*} (t₀ q : ℝ) (p : α × ℝ) : α × ℝ := (p.1, (p.2 - t₀) / q)

theorem measurable_rescale {α : Type*} [MeasurableSpace α] (t₀ q : ℝ) :
    Measurable (rescale (α := α) t₀ q) := by
  unfold rescale
  exact measurable_fst.prodMk ((measurable_snd.sub_const t₀).div_const q)

/-- Lebesgue measure of a preimage under the affine block map. -/
theorem volume_preimage_block (t₀ q : ℝ) (hq : 0 < q) (s : Set ℝ) :
    volume ((fun t : ℝ => (t - t₀) / q) ⁻¹' s) = ENNReal.ofReal q * volume s := by
  have h1 : (fun t : ℝ => (t - t₀) / q) ⁻¹' s =
      (fun t : ℝ => t + (-t₀)) ⁻¹' ((fun x : ℝ => q⁻¹ * x) ⁻¹' s) := by
    ext t; simp [div_eq_inv_mul, sub_eq_add_neg]
  rw [h1, measure_preimage_add_right, Real.volume_preimage_mul_left (inv_ne_zero hq.ne'),
    inv_inv, abs_of_pos hq]

theorem map_rescale_le {α : Type*} [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    (m : Measure (α × ℝ)) (A : Set α) (hA : MeasurableSet A) (t₀ q K : ℝ) (hq : 0 < q)
    (hK : 0 ≤ K) (hm : m ≤ ENNReal.ofReal K • ν.prod volume) (hsupp : m (A ×ˢ Icc t₀ (t₀ + q))ᶜ = 0) :
    m.map (rescale t₀ q) ≤ ENNReal.ofReal (K * q) • (ν.restrict A).prod volume := by
  rw [Measure.le_iff]
  intro E hE
  have hf := measurable_rescale (α := α) t₀ q
  rw [Measure.map_apply hf hE]
  have hAI : MeasurableSet (A ×ˢ Icc t₀ (t₀ + q)) := hA.prod measurableSet_Icc
  have hpre : MeasurableSet (rescale t₀ q ⁻¹' E) := hf hE
  calc m (rescale t₀ q ⁻¹' E)
      ≤ m (rescale t₀ q ⁻¹' E ∩ A ×ˢ Icc t₀ (t₀ + q)) + m (A ×ˢ Icc t₀ (t₀ + q))ᶜ := by
        calc m (rescale t₀ q ⁻¹' E)
            ≤ m ((rescale t₀ q ⁻¹' E ∩ A ×ˢ Icc t₀ (t₀ + q)) ∪ (A ×ˢ Icc t₀ (t₀ + q))ᶜ) := by
              apply measure_mono
              intro p hp
              by_cases h : p ∈ A ×ˢ Icc t₀ (t₀ + q)
              · exact Or.inl ⟨hp, h⟩
              · exact Or.inr h
          _ ≤ _ := measure_union_le _ _
    _ = m (rescale t₀ q ⁻¹' E ∩ A ×ˢ Icc t₀ (t₀ + q)) := by rw [hsupp, add_zero]
    _ ≤ (ENNReal.ofReal K • ν.prod volume) (rescale t₀ q ⁻¹' E ∩ A ×ˢ Icc t₀ (t₀ + q)) :=
        hm _
    _ ≤ ENNReal.ofReal K * (ν.prod volume) (rescale t₀ q ⁻¹' E ∩ A ×ˢ univ) := by
        rw [Measure.smul_apply, smul_eq_mul]
        gcongr
        exact subset_univ _
    _ = ENNReal.ofReal K * ∫⁻ l, A.indicator (fun l => volume
          ((fun t : ℝ => (t - t₀) / q) ⁻¹' (Prod.mk l ⁻¹' E))) l ∂ν := by
        rw [Measure.prod_apply (hpre.inter (hA.prod MeasurableSet.univ))]
        congr 1
        apply lintegral_congr
        intro l
        by_cases hl : l ∈ A
        · rw [indicator_of_mem hl]
          congr 1
          ext t; simp [rescale, hl]
        · rw [indicator_of_notMem hl]
          have : Prod.mk l ⁻¹' (rescale t₀ q ⁻¹' E ∩ A ×ˢ univ) = ∅ := by
            ext t; simp [hl]
          rw [this, measure_empty]
    _ = ENNReal.ofReal K * ∫⁻ l, A.indicator (fun l => ENNReal.ofReal q *
          volume (Prod.mk l ⁻¹' E)) l ∂ν := by
        congr 1
        apply lintegral_congr
        intro l
        by_cases hl : l ∈ A
        · rw [indicator_of_mem hl, indicator_of_mem hl, volume_preimage_block t₀ q hq]
        · rw [indicator_of_notMem hl, indicator_of_notMem hl]
    _ = ENNReal.ofReal (K * q) * ((ν.restrict A).prod volume) E := by
        rw [Measure.prod_apply hE, lintegral_indicator hA,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
          ENNReal.ofReal_mul hK]
    _ = _ := by rw [Measure.smul_apply, smul_eq_mul]

theorem measurableEmbedding_rescale {α : Type*} [MeasurableSpace α] (t₀ q : ℝ) (hq : q ≠ 0) :
    MeasurableEmbedding (rescale (α := α) t₀ q) := by
  refine MeasurableEmbedding.of_measurable_inverse (g := fun p : α × ℝ => (p.1, t₀ + q * p.2))
    (measurable_rescale t₀ q) ?_ ?_ ?_
  · -- the range is everything
    have : Set.range (rescale (α := α) t₀ q) = univ := by
      apply eq_univ_of_forall
      intro p
      refine ⟨(p.1, t₀ + q * p.2), ?_⟩
      simp only [rescale]
      ext
      · rfl
      · simp only; field_simp; ring
    rw [this]; exact MeasurableSet.univ
  · exact measurable_fst.prodMk (measurable_const.add (measurable_const.mul measurable_snd))
  · intro p
    simp only [rescale]
    ext
    · rfl
    · simp only; field_simp; ring

/-- Rescaled measure of any set. -/
theorem map_rescale_apply {α : Type*} [MeasurableSpace α] (m : Measure (α × ℝ)) (t₀ q : ℝ)
    (hq : q ≠ 0) (E : Set (α × ℝ)) :
    (m.map (rescale t₀ q)) E = m (rescale t₀ q ⁻¹' E) :=
  (measurableEmbedding_rescale t₀ q hq).map_apply m E

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
