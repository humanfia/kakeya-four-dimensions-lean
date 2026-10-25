import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_pair_atlas_assembly

open MeasureTheory Set

/-- A source-time rectangle over an arbitrary event in the original one-time law. -/
theorem pair_rectangle_measure {α : Type*} [MeasurableSpace α]
    (ν : Measure α) {B : Set ℝ} (hB : MeasurableSet B)
    {U : Set (α × ℝ)} (hU : MeasurableSet U) :
    (ν.prod (volume.prod volume))
        {z : α × (ℝ × ℝ) | z.2.1 ∈ B ∧ (z.1, z.2.2) ∈ U} =
      volume B * (ν.prod volume) U := by
  have hm : MeasurableSet
      {z : α × (ℝ × ℝ) | z.2.1 ∈ B ∧ (z.1, z.2.2) ∈ U} :=
    (hB.preimage (by fun_prop)).inter (hU.preimage (by fun_prop))
  rw [Measure.prod_apply hm]
  change (∫⁻ l, (volume.prod volume) (B ×ˢ {t : ℝ | (l, t) ∈ U}) ∂ν) = _
  simp_rw [Measure.prod_prod]
  rw [Measure.prod_apply hU]
  exact lintegral_const_mul _ (measurable_measure_prodMk_left hU)

/-- Finite source-block averaging keeps the original later-incidence law. The source events
may be enlarged to full old assignments before selecting a block. -/
theorem finite_source_selection {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] [Nonempty ι] (ν : Measure α)
    (B : ι → Set ℝ) (U : ι → Set (α × ℝ))
    (hB : ∀ j, MeasurableSet (B j)) (hU : ∀ j, MeasurableSet (U j))
    (S : Set (α × (ℝ × ℝ)))
    (hcover : S ⊆ ⋃ j, {z : α × (ℝ × ℝ) |
      z.2.1 ∈ B j ∧ (z.1, z.2.2) ∈ U j})
    (q c : ENNReal) (hvol : ∀ j, volume (B j) = q)
    (hscale : c * (Fintype.card ι : ENNReal) * q = 1) :
    ∃ j : ι, c * (ν.prod (volume.prod volume)) S ≤ (ν.prod volume) (U j) := by
  classical
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ
    (fun j => (ν.prod volume) (U j)) Finset.univ_nonempty
  refine ⟨j, ?_⟩
  calc
    c * (ν.prod (volume.prod volume)) S ≤
        c * (ν.prod (volume.prod volume))
          (⋃ i, {z : α × (ℝ × ℝ) | z.2.1 ∈ B i ∧ (z.1, z.2.2) ∈ U i}) :=
      mul_le_mul_right (measure_mono hcover) _
    _ ≤ c * ∑ i : ι, (ν.prod (volume.prod volume))
          {z : α × (ℝ × ℝ) | z.2.1 ∈ B i ∧ (z.1, z.2.2) ∈ U i} :=
      mul_le_mul_right (measure_iUnion_fintype_le _ _) _
    _ = c * ∑ i : ι, q * (ν.prod volume) (U i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [pair_rectangle_measure ν (hB i) (hU i), hvol]
    _ ≤ c * ∑ _i : ι, q * (ν.prod volume) (U j) := by
      apply mul_le_mul_right
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_right (hj i (Finset.mem_univ i)) q
    _ = (ν.prod volume) (U j) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, ← mul_assoc, hscale, one_mul]

end Submission.Obl.k4_scalar_pair_atlas_assembly
