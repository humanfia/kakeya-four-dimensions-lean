import Mathlib
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.MassBounds

/-! Finite observation lists and weighted crossing budgets. -/

namespace Submission.Obl.k4_scalar_true_atlas_terminal_lists

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable def labelsAt {Z : Type*} {W n : ℕ} (γ : Fin n → Fin W)
    (X : Fin n → Set Z) (a : Fin W) (z : Z) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => γ i = a ∧ z ∈ X i)

theorem labelsAt_card {Z : Type*} {W n : ℕ} (γ : Fin n → Fin W)
    (X : Fin n → Set Z) (a : Fin W) (z : Z) :
    ((labelsAt γ X a z).card : ENNReal) =
      ∑ i, (if γ i = a then X i else ∅).indicator (fun _ => (1 : ENNReal)) z := by
  classical
  calc
    _ = ∑ i ∈ labelsAt γ X a z, (1 : ENNReal) := by simp
    _ = _ := by
      simp only [labelsAt, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases ha : γ i = a <;> by_cases hz : z ∈ X i <;> simp [ha, hz]

theorem labelsAt_card_measurable {Z : Type*} [MeasurableSpace Z] {W n : ℕ}
    (γ : Fin n → Fin W) (X : Fin n → Set Z) (hX : ∀ i, MeasurableSet (X i))
    (a : Fin W) : Measurable (fun z => ((labelsAt γ X a z).card : ENNReal)) := by
  classical
  simp_rw [labelsAt_card]
  apply Finset.measurable_sum
  intro i _
  apply measurable_const.indicator
  split_ifs <;> simp_all

theorem labelsAt_card_integral {Z : Type*} [MeasurableSpace Z] {W n : ℕ}
    (γ : Fin n → Fin W) (X : Fin n → Set Z) (hX : ∀ i, MeasurableSet (X i))
    (a : Fin W) (μ : Measure Z) :
    (∫⁻ z, ((labelsAt γ X a z).card : ENNReal) ∂μ) =
      ∑ i, if γ i = a then μ (X i) else 0 := by
  classical
  simp_rw [labelsAt_card]
  rw [lintegral_finsetSum _ (fun i _ => by
    apply measurable_const.indicator
    split_ifs <;> simp_all)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha : γ i = a
  · simp only [ha, ite_true]
    rw [lintegral_indicator_const (hX i), one_mul]
  · simp [ha]

/-- Weighted Markov bound for the number of geometrically compatible labels.
Each chart is charged in its own original world law. -/
theorem weighted_crossing_tail {Z : Type*} [MeasurableSpace Z] {W n : ℕ}
    (γ : Fin n → Fin W) (X : Fin n → Set Z) (hX : ∀ i, MeasurableSet (X i))
    (ω : Fin W → ENNReal) (μ : Fin W → Measure Z) (R : ENNReal) :
    R * (∑ a, ω a * μ a {z | R < ((labelsAt γ X a z).card : ENNReal)}) ≤
      ∑ i, ω (γ i) * μ (γ i) (X i) := by
  classical
  have hmark (a : Fin W) :
      R * μ a {z | R < ((labelsAt γ X a z).card : ENNReal)} ≤
        ∑ i, if γ i = a then μ a (X i) else 0 := by
    calc
      _ ≤ R * μ a {z | R ≤ ((labelsAt γ X a z).card : ENNReal)} := by
        gcongr
        exact fun hz => hz.le
      _ ≤ ∫⁻ z, ((labelsAt γ X a z).card : ENNReal) ∂μ a :=
        mul_meas_ge_le_lintegral (labelsAt_card_measurable γ X hX a) R
      _ = _ := labelsAt_card_integral γ X hX a (μ a)
  calc
    _ = ∑ a, ω a * (R * μ a {z | R < ((labelsAt γ X a z).card : ENNReal)}) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ ∑ a, ω a * (∑ i, if γ i = a then μ a (X i) else 0) := by
      gcongr with a
      exact hmark a
    _ = ∑ i, ω (γ i) * μ (γ i) (X i) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp

/-- Deleting large crossing lists produces a measurable policy satisfying
its list-size constraint at every observation. -/
noncomputable def boundedLabels {Z : Type*} {W n : ℕ} (γ : Fin n → Fin W)
    (X : Fin n → Set Z) (R : ℝ) (a : Fin W) (z : Z) : Finset (Fin n) :=
  if ((labelsAt γ X a z).card : ℝ) ≤ R then labelsAt γ X a z else ∅

theorem boundedLabels_card {Z : Type*} {W n : ℕ} (γ : Fin n → Fin W)
    (X : Fin n → Set Z) {R : ℝ} (hR : 0 ≤ R) (a : Fin W) (z : Z) :
    ((boundedLabels γ X R a z).card : ℝ) ≤ R := by
  unfold boundedLabels
  split_ifs with h
  · exact h
  · simpa using hR

theorem boundedLabels_measurable {Z : Type*} [MeasurableSpace Z] {W n : ℕ}
    (γ : Fin n → Fin W) (X : Fin n → Set Z) (hX : ∀ i, MeasurableSet (X i))
    (R : ℝ) (a : Fin W) (i : Fin n) :
    MeasurableSet {z | i ∈ boundedLabels γ X R a z} := by
  classical
  have hcount : Measurable (fun z => ((labelsAt γ X a z).card : ℝ)) := by
    convert (labelsAt_card_measurable γ X hX a).ennreal_toReal using 1
    simp
  have hid : {z | i ∈ boundedLabels γ X R a z} =
      {z | ((labelsAt γ X a z).card : ℝ) ≤ R} ∩ {z | γ i = a ∧ z ∈ X i} := by
    ext z
    change (i ∈ (if ((labelsAt γ X a z).card : ℝ) ≤ R then labelsAt γ X a z else ∅)) ↔ _
    by_cases h : ((labelsAt γ X a z).card : ℝ) ≤ R
    · rw [ite_eq_left h]
      simp only [mem_inter_iff, mem_ofPred_eq, h, true_and]
      simp [labelsAt]
    · rw [ite_eq_right h]
      simp only [Finset.notMem_empty, mem_inter_iff, mem_ofPred_eq, h, false_and]
  rw [hid]
  apply (measurableSet_le hcount measurable_const).inter
  by_cases ha : γ i = a <;> simp [ha, hX i]

/-- On the part of the original law below a density ceiling, crossing
multiplicity is charged to the reference volumes of the crossing sets. -/
theorem capped_crossing_tail {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    {W n : ℕ} (γ : Fin n → Fin W) (X : Fin n → Set Z)
    (hX : ∀ i, MeasurableSet (X i)) (ω : Fin W → ENNReal)
    (μ : Fin W → Measure Y) (ρ : Measure Z) (φ : Y → Z) (hφ : Measurable φ)
    (g : Fin W → Z → ENNReal) (hg : ∀ a, Measurable (g a))
    (hlaw : ∀ a, (μ a).map φ = ρ.withDensity (g a)) (R θ : ENNReal) :
    R * (∑ a, ω a * μ a {q | R < ((labelsAt γ X a (φ q)).card : ENNReal) ∧
      g a (φ q) ≤ θ}) ≤ θ * (∑ i, ω (γ i) * ρ (X i)) := by
  let ν : Fin W → Measure Z := fun a =>
    ((μ a).map φ).restrict {z | g a z ≤ θ}
  have hν (a : Fin W) (i : Fin n) : ν a (X i) ≤ θ * ρ (X i) := by
    have hcap : MeasurableSet {z | g a z ≤ θ} := measurableSet_le (hg a) measurable_const
    calc
      _ = (ρ.withDensity (g a)) (X i ∩ {z | g a z ≤ θ}) := by
        change (((μ a).map φ).restrict {z | g a z ≤ θ}) (X i) = _
        rw [Measure.restrict_apply (hX i), hlaw a]
      _ = ∫⁻ z in X i ∩ {z | g a z ≤ θ}, g a z ∂ρ :=
        withDensity_apply _ ((hX i).inter hcap)
      _ ≤ ∫⁻ _z in X i ∩ {z | g a z ≤ θ}, θ ∂ρ :=
        setLIntegral_mono measurable_const (fun z hz => hz.2)
      _ = θ * ρ (X i ∩ {z | g a z ≤ θ}) := setLIntegral_const _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (measure_mono inter_subset_left) zero_le
  have htail (a : Fin W) :
      ν a {z | R < ((labelsAt γ X a z).card : ENNReal)} =
        μ a {q | R < ((labelsAt γ X a (φ q)).card : ENNReal) ∧ g a (φ q) ≤ θ} := by
    have hcrowd : MeasurableSet {z | R < ((labelsAt γ X a z).card : ENNReal)} :=
      measurableSet_lt measurable_const (labelsAt_card_measurable γ X hX a)
    have hcap : MeasurableSet {z | g a z ≤ θ} := measurableSet_le (hg a) measurable_const
    change (((μ a).map φ).restrict {z | g a z ≤ θ}) {z | R < ((labelsAt γ X a z).card : ENNReal)} = _
    rw [Measure.restrict_apply hcrowd, Measure.map_apply hφ (hcrowd.inter hcap)]
    rfl
  calc
    _ = R * (∑ a, ω a * ν a {z | R < ((labelsAt γ X a z).card : ENNReal)}) := by
      simp only [htail]
    _ ≤ ∑ i, ω (γ i) * ν (γ i) (X i) := weighted_crossing_tail γ X hX ω ν R
    _ ≤ ∑ i, ω (γ i) * (θ * ρ (X i)) := by
      gcongr with i
      exact hν (γ i) i
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- A true-floor budget converts the reference-volume Markov estimate into
a uniform bound that is independent of the total number of charts. -/
theorem capped_crossing_tail_of_budget {Y Z : Type*}
    [MeasurableSpace Y] [MeasurableSpace Z] {W n : ℕ}
    (γ : Fin n → Fin W) (X : Fin n → Set Z) (hX : ∀ i, MeasurableSet (X i))
    (ω : Fin W → ENNReal) (μ : Fin W → Measure Y) (ρ : Measure Z)
    (φ : Y → Z) (hφ : Measurable φ) (g : Fin W → Z → ENNReal)
    (hg : ∀ a, Measurable (g a)) (hlaw : ∀ a, (μ a).map φ = ρ.withDensity (g a))
    (C : Fin n → Set Y) (R θ H : ENNReal)
    (hbudget : (∑ i, ω (γ i) * μ (γ i) (C i)) ≤ 1)
    (hfloor : ∀ i, θ * ρ (X i) ≤ H * μ (γ i) (C i)) :
    R * (∑ a, ω a * μ a {q | R < ((labelsAt γ X a (φ q)).card : ENNReal) ∧
      g a (φ q) ≤ θ}) ≤ H := by
  calc
    _ ≤ θ * (∑ i, ω (γ i) * ρ (X i)) :=
      capped_crossing_tail γ X hX ω μ ρ φ hφ g hg hlaw R θ
    _ = ∑ i, ω (γ i) * (θ * ρ (X i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, ω (γ i) * (H * μ (γ i) (C i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hfloor i) zero_le
    _ = H * (∑ i, ω (γ i) * μ (γ i) (C i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ H * 1 := mul_le_mul_of_nonneg_left hbudget zero_le
    _ = H := mul_one H

theorem labelsAt_card_real_measurable {Z : Type*} [MeasurableSpace Z] {W n : ℕ}
    (γ : Fin n → Fin W) (X : Fin n → Set Z) (hX : ∀ i, MeasurableSet (X i))
    (a : Fin W) : Measurable (fun z => ((labelsAt γ X a z).card : ℝ)) := by
  convert (labelsAt_card_measurable γ X hX a).ennreal_toReal using 1
  simp

theorem mem_boundedLabels {Z : Type*} {W n : ℕ} (γ : Fin n → Fin W)
    (X : Fin n → Set Z) (R : ℝ) (a : Fin W) (z : Z) (i : Fin n) :
    i ∈ boundedLabels γ X R a z ↔
      ((labelsAt γ X a z).card : ℝ) ≤ R ∧ γ i = a ∧ z ∈ X i := by
  classical
  unfold boundedLabels
  split_ifs with h
  · simp only [h, true_and]
    simp [labelsAt]
  · simp only [h, false_and, Finset.notMem_empty]

/-- An injective relabeling does not increase the size of any list. -/
theorem reindexed_list_card {m n : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (L : Finset (Fin n)) : (Finset.univ.filter (fun i => e i ∈ L)).card ≤ L.card := by
  classical
  calc
    _ = ((Finset.univ.filter (fun i => e i ∈ L)).image e).card :=
      (Finset.card_image_of_injective _ he).symm
    _ ≤ L.card := Finset.card_le_card (by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp hj).2)

end Submission.Obl.k4_scalar_true_atlas_terminal_lists
