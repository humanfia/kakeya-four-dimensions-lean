import Submission.Obl.k4_initial_horizon_bound.Duration

set_option autoImplicit false

/-! Summing short labeled portions against the original trajectory prior. -/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Submission.Obl.k4_initial_horizon_bound

variable {α ι : Type*} [MeasurableSpace α] [Countable ι]

/-- The cost depends on the number of entries met by each original trajectory,
rather than the total number of labels in the ambient table. -/
theorem counted_short_duration_mass_le (ν : Measure α)
    {E : ι → Set (α × ℝ)} (hE : ∀ i, MeasurableSet (E i))
    (L : α → Finset ι) (a D : ℝ≥0∞)
    (hcount : ∀ l, ((L l).card : ℝ≥0∞) ≤ D)
    (hsupport : ∀ l i, incidenceDuration (E i) l ≠ 0 → i ∈ L l) :
    (∑' i, (ν.withDensity (incidenceDuration (E i)))
      {l | incidenceDuration (E i) l < a}) ≤ a * D * ν univ := by
  classical
  let S : ι → Set α := fun i => {l | incidenceDuration (E i) l < a}
  let f : ι → α → ℝ≥0∞ := fun i => (S i).indicator (incidenceDuration (E i))
  have hS (i : ι) : MeasurableSet (S i) :=
    measurableSet_lt (measurable_incidenceDuration (hE i)) measurable_const
  have hf (i : ι) : Measurable (f i) :=
    (measurable_incidenceDuration (hE i)).indicator (hS i)
  have hfle (i : ι) (l : α) : f i l ≤ a := by
    by_cases h : l ∈ S i
    · simpa only [f, indicator_of_mem h] using (le_of_lt h)
    · simp only [f, indicator_of_notMem h, zero_le]
  have hpoint (l : α) : (∑' i, f i l) ≤ a * D := by
    have hzero (i : ι) (hi : i ∉ L l) : f i l = 0 := by
      have hd : incidenceDuration (E i) l = 0 := by
        by_contra hd
        exact hi (hsupport l i hd)
      simp only [f, indicator_apply, hd, ite_self]
    rw [tsum_eq_sum hzero]
    calc
      (∑ i ∈ L l, f i l) ≤ ∑ _i ∈ L l, a :=
        Finset.sum_le_sum (fun i _ => hfle i l)
      _ = ((L l).card : ℝ≥0∞) * a := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ D * a := mul_le_mul_of_nonneg_right (hcount l) zero_le
      _ = a * D := mul_comm _ _
  calc
    _ = ∑' i, ∫⁻ l, f i l ∂ν := by
      apply tsum_congr
      intro i
      rw [withDensity_apply _ (hS i), ← lintegral_indicator (hS i)]
    _ = ∫⁻ l, ∑' i, f i l ∂ν := (lintegral_tsum (fun i => (hf i).aemeasurable)).symm
    _ ≤ ∫⁻ _l : α, a * D ∂ν := lintegral_mono hpoint
    _ = a * D * ν univ := by simp only [lintegral_const]

theorem counted_short_incidence_mass_le (ν : Measure α) [SFinite ν]
    {E : ι → Set (α × ℝ)} (hE : ∀ i, MeasurableSet (E i))
    (L : α → Finset ι) (a D : ℝ≥0∞)
    (hcount : ∀ l, ((L l).card : ℝ≥0∞) ≤ D)
    (hsupport : ∀ l i, incidenceDuration (E i) l ≠ 0 → i ∈ L l) :
    (∑' i, (ν.prod volume)
      (E i ∩ ({l | incidenceDuration (E i) l < a} ×ˢ univ))) ≤ a * D * ν univ := by
  have heq (i : ι) :
      (ν.withDensity (incidenceDuration (E i))) {l | incidenceDuration (E i) l < a} =
        (ν.prod volume) (E i ∩ ({l | incidenceDuration (E i) l < a} ×ˢ univ)) :=
    duration_withDensity_apply ν (hE i)
      (measurableSet_lt (measurable_incidenceDuration (hE i)) measurable_const)
  simpa only [heq] using counted_short_duration_mass_le ν hE L a D hcount hsupport

/-- The same deletion budget transfers through the original incidence-density
ceiling. The trajectory prior in the right side is unchanged. -/
theorem counted_short_incidence_deletion_le (ν : Measure α) [SFinite ν]
    (μ : Measure (α × ℝ)) {c : ℝ≥0∞} (hdom : μ ≤ c • (ν.prod volume))
    {E : ι → Set (α × ℝ)} (hE : ∀ i, MeasurableSet (E i))
    (L : α → Finset ι) (a D : ℝ≥0∞)
    (hcount : ∀ l, ((L l).card : ℝ≥0∞) ≤ D)
    (hsupport : ∀ l i, incidenceDuration (E i) l ≠ 0 → i ∈ L l) :
    μ (⋃ i, E i ∩ ({l | incidenceDuration (E i) l < a} ×ˢ univ)) ≤
      c * (a * D * ν univ) := by
  calc
    _ ≤ (c • (ν.prod volume))
        (⋃ i, E i ∩ ({l | incidenceDuration (E i) l < a} ×ˢ univ)) := hdom _
    _ = c * (ν.prod volume)
        (⋃ i, E i ∩ ({l | incidenceDuration (E i) l < a} ×ˢ univ)) := by
      rw [Measure.smul_apply]
      rfl
    _ ≤ c * ∑' i, (ν.prod volume)
        (E i ∩ ({l | incidenceDuration (E i) l < a} ×ˢ univ)) :=
      mul_le_mul_of_nonneg_left (measure_iUnion_le _) zero_le
    _ ≤ c * (a * D * ν univ) := mul_le_mul_of_nonneg_left
      (counted_short_incidence_mass_le ν hE L a D hcount hsupport) zero_le

theorem record_short_incidence_deletion_le [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure α) [SFinite ν] (μ : Measure (α × ℝ))
    {c : ℝ≥0∞} (hdom : μ ≤ c • (ν.prod volume))
    {E : Set (α × ℝ)} (hE : MeasurableSet E)
    (record : α × ℝ → ι) (hrecord : Measurable record)
    (L : α → Finset ι) (a D : ℝ≥0∞)
    (hcount : ∀ l, ((L l).card : ℝ≥0∞) ≤ D)
    (hlist : ∀ p ∈ E, record p ∈ L p.1) :
    μ {p | p ∈ E ∧ incidenceDuration (E ∩ record ⁻¹' {record p}) p.1 < a} ≤
      c * (a * D * ν univ) := by
  let E' : ι → Set (α × ℝ) := fun i => E ∩ record ⁻¹' {i}
  have hE' (i : ι) : MeasurableSet (E' i) :=
    hE.inter (hrecord (measurableSet_singleton i))
  have hsupport (l : α) (i : ι) (hd : incidenceDuration (E' i) l ≠ 0) : i ∈ L l := by
    obtain ⟨t, ht⟩ := nonempty_of_measure_ne_zero hd
    have hli : record (l, t) = i := ht.2
    simpa only [hli] using hlist (l, t) ht.1
  have heq : {p | p ∈ E ∧ incidenceDuration (E ∩ record ⁻¹' {record p}) p.1 < a} =
      ⋃ i, E' i ∩ ({l | incidenceDuration (E' i) l < a} ×ˢ univ) := by
    ext p
    constructor
    · rintro ⟨hp, hd⟩
      exact mem_iUnion.mpr ⟨record p, ⟨⟨hp, rfl⟩, hd, mem_univ _⟩⟩
    · intro hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      have heq : record p = i := hi.1.2
      refine ⟨hi.1.1, ?_⟩
      change incidenceDuration (E' (record p)) p.1 < a
      rw [heq]
      exact hi.2.1
  rw [heq]
  exact counted_short_incidence_deletion_le ν μ hdom hE' L a D hcount hsupport

end Submission.Obl.k4_scalar_grid_polynomial_qualification
