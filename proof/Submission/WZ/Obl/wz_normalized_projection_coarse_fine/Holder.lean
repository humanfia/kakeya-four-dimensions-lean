-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.Holder.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set MeasureTheory
open scoped ENNReal

noncomputable section

def multiplicity {ι α : Type*} [Fintype ι] (S : ι → Set α) (p : α) : ℝ≥0∞ :=
  ∑ i, (S i).indicator (fun _ => 1) p

lemma measurable_multiplicity {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    {S : ι → Set α} (hS : ∀ i, MeasurableSet (S i)) : Measurable (multiplicity S) := by
  exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hS i))

lemma lintegral_multiplicity {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    {S : ι → Set α} (hS : ∀ i, MeasurableSet (S i)) (μ : Measure α) :
    ∫⁻ p, multiplicity S p ∂μ = ∑ i, μ (S i) := by
  simp only [multiplicity]
  rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator (hS i))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lintegral_indicator (hS i)]
  simp

/-- The cubic form of Hölder gives an area lower bound from an `L^(3/2)` moment. -/
theorem sum_measure_cubed_le_moment {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) {S T : ι → Set α} {E : Set α}
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ i, MeasurableSet (T i))
    (hE : MeasurableSet E) (hTS : ∀ i, T i ⊆ S i) (hTE : ∀ i, T i ⊆ E) :
    (∑ i, μ (T i)) ^ 3 ≤ μ E * (∫⁻ p, multiplicity S p ^ (3 / 2 : ℝ) ∂μ) ^ 2 := by
  classical
  let u : α → ℝ≥0∞ := E.indicator (fun _ => 1)
  have hu : Measurable u := measurable_const.indicator hE
  have hm : Measurable (multiplicity S) := measurable_multiplicity hS
  have hdom : ∀ p, multiplicity T p ≤ u p * multiplicity S p := by
    intro p
    by_cases hp : p ∈ E
    · simp only [u, indicator_of_mem hp, one_mul]
      apply Finset.sum_le_sum
      intro i hi
      by_cases hiT : p ∈ T i
      · simp [hiT, hTS i hiT]
      · simp [hiT]
    · have hnot (i : ι) : p ∉ T i := fun hi => hp (hTE i hi)
      simp [multiplicity, u, hp, hnot]
  have hmass : ∑ i, μ (T i) ≤ ∫⁻ p, u p * multiplicity S p ∂μ := by
    rw [← lintegral_multiplicity hT μ]
    exact lintegral_mono hdom
  have hconj : (3 : ℝ).HolderConjugate (3 / 2) := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj hu.aemeasurable hm.aemeasurable
  have hu3 : ∫⁻ p, u p ^ (3 : ℝ) ∂μ = μ E := by
    have he : (fun p => u p ^ (3 : ℝ)) = u := by
      funext p
      by_cases hp : p ∈ E <;> simp [u, hp]
    rw [he, lintegral_indicator hE]
    simp
  rw [hu3] at hholder
  have h := pow_le_pow_left' (hmass.trans hholder) 3
  rw [mul_pow] at h
  have hcube (a : ℝ≥0∞) : (a ^ (1 / 3 : ℝ)) ^ 3 = a := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have htwo (a : ℝ≥0∞) : (a ^ (1 / (3 / 2) : ℝ)) ^ 3 = a ^ 2 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rwa [hcube, htwo] at h

/-- Outer-volume version, obtained with measurable hulls inside the measurable majorants. -/
theorem sum_outer_measure_cubed_le_moment {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) {S T : ι → Set α}
    (hS : ∀ i, MeasurableSet (S i)) (hTS : ∀ i, T i ⊆ S i) :
    (∑ i, μ (T i)) ^ 3 ≤ μ (⋃ i, T i) *
      (∫⁻ p, multiplicity S p ^ (3 / 2 : ℝ) ∂μ) ^ 2 := by
  let E := toMeasurable μ (⋃ i, T i)
  let U : ι → Set α := fun i => toMeasurable μ (T i) ∩ S i ∩ E
  have hU (i : ι) : MeasurableSet (U i) :=
    ((measurableSet_toMeasurable _ _).inter (hS i)).inter (measurableSet_toMeasurable _ _)
  have hTU (i : ι) : T i ⊆ U i := fun p hp =>
    ⟨⟨subset_toMeasurable μ (T i) hp, hTS i hp⟩,
      subset_toMeasurable μ (⋃ i, T i) (mem_iUnion.mpr ⟨i, hp⟩)⟩
  have hvol (i : ι) : μ (U i) = μ (T i) := by
    apply le_antisymm _ (measure_mono (hTU i))
    exact (measure_mono (show U i ⊆ toMeasurable μ (T i) from
      inter_subset_left.trans inter_subset_left)).trans_eq (measure_toMeasurable _)
  have h := sum_measure_cubed_le_moment μ hS hU (measurableSet_toMeasurable _ _)
    (fun _ => inter_subset_left.trans inter_subset_right) (fun _ => inter_subset_right)
  simpa only [hvol, measure_toMeasurable] using h

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
