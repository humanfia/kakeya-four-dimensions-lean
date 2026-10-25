-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/PairMerge.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.PairLaw

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory Set Finset

section Density

variable {α β : Type*} [Fintype α] [DecidableEq β]

/-- Densities are merged by their geometric label; the raw candidate index is discarded. -/
noncomputable def mergedDensity (label : α → β) (p : α → ℝ) (b : β) : ℝ := by
  classical
  exact ∑ a, if label a = b then p a else 0

theorem mergedDensity_nonneg (label : α → β) {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (b : β) :
    0 ≤ mergedDensity label p b := by
  classical
  apply sum_nonneg
  intro a _
  split_ifs <;> first | exact hp a | exact le_rfl

theorem sum_mergedDensity [Fintype β] (label : α → β) (p : α → ℝ) :
    ∑ b, mergedDensity label p b = ∑ a, p a := by
  classical
  unfold mergedDensity
  rw [sum_comm]
  simp

/-- Independent posterior pairing commutes with finite label merging. -/
theorem posteriorPairDensity_merge [Fintype β] (label : α → β) (p : α → ℝ) (b c : β) :
    (∑ a, ∑ a', if label a = b ∧ label a' = c then posteriorPairDensity p a a' else 0) =
      posteriorPairDensity (mergedDensity label p) b c := by
  classical
  have heq (a a' : α) :
      (if label a = b ∧ label a' = c then posteriorPairDensity p a a' else 0) =
        (if label a = b then p a else 0) * (if label a' = c then p a' else 0) /
          (∑ d, p d) := by
    by_cases ha : label a = b <;> by_cases ha' : label a' = c <;>
      simp [ha, ha', posteriorPairDensity]
  simp_rw [heq, ← sum_div, ← mul_sum, ← sum_mul]
  rw [posteriorPairDensity, sum_mergedDensity]
  rfl

end Density

section IndexedLaw

variable {α β X : Type*} [Fintype α] [Fintype β] [DecidableEq β]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace X]

/-- Finite indexed density laws commute with every deterministic merging of their indices. -/
theorem indexedLaw_map_labels (μ : Measure X) (f : α → X → ENNReal)
    (hf : ∀ a, Measurable (f a)) (label : α → β) :
    (Submission.Obl.k4_original_prior_line_extraction.indexedLaw μ f).map
      (fun p => (label p.1, p.2)) =
      Submission.Obl.k4_original_prior_line_extraction.indexedLaw μ
        (fun b x => ∑ a, if label a = b then f a x else 0) := by
  classical
  have hm : Measurable (fun p : α × X => (label p.1, p.2)) :=
    ((measurable_of_countable label).comp measurable_fst).prodMk measurable_snd
  have hd (a : α) (b : β) : Measurable (fun x => if label a = b then f a x else 0) := by
    split_ifs <;> first | exact hf a | exact measurable_const
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply hm hE,
    Submission.Obl.k4_original_prior_line_extraction.indexedLaw_apply μ f (hE.preimage hm),
    Submission.Obl.k4_original_prior_line_extraction.indexedLaw_apply μ _ hE]
  change (∑ a, ∫⁻ x in {x | (label a, x) ∈ E}, f a x ∂μ) =
    ∑ b, ∫⁻ x in {x | (b, x) ∈ E}, ∑ a, if label a = b then f a x else 0 ∂μ
  have hsum (b : β) :
      (∫⁻ x in {x | (b, x) ∈ E}, ∑ a, if label a = b then f a x else 0 ∂μ) =
        ∑ a, ∫⁻ x in {x | (b, x) ∈ E}, if label a = b then f a x else 0 ∂μ :=
    lintegral_finsetSum univ (fun a _ => hd a b)
  simp_rw [hsum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  have hterm (b : β) :
      (∫⁻ x in {x | (b, x) ∈ E}, if label a = b then f a x else 0 ∂μ) =
        if label a = b then ∫⁻ x in {x | (b, x) ∈ E}, f a x ∂μ else 0 := by
    split_ifs <;> simp
  simp_rw [hterm]
  simp

/-- Merging the posterior pair law gives the posterior pair law of the merged densities.
This keeps the original observation and all aggregate agreement mass. -/
theorem posteriorPairLaw_merge (μ : Measure X) (p : X → α → ℝ)
    (hpmeas : ∀ a, Measurable (fun x => p x a)) (hp : ∀ x a, 0 ≤ p x a) (label : α → β) :
    (posteriorPairLaw μ p).map (fun q => ((label q.1.1, label q.1.2), q.2)) =
      posteriorPairLaw μ (fun x => mergedDensity label (p x)) := by
  classical
  have hd (a : α × α) : Measurable (fun x =>
      ENNReal.ofReal (posteriorPairDensity (p x) a.1 a.2)) := by
    unfold posteriorPairDensity
    fun_prop
  rw [posteriorPairLaw,
    indexedLaw_map_labels μ _ hd (fun a : α × α => (label a.1, label a.2))]
  unfold posteriorPairLaw
  congr 1
  funext b x
  have heq (a : α × α) :
      (if (label a.1, label a.2) = b then
        ENNReal.ofReal (posteriorPairDensity (p x) a.1 a.2) else 0) =
      ENNReal.ofReal (if (label a.1, label a.2) = b then
        posteriorPairDensity (p x) a.1 a.2 else 0) := by split_ifs <;> simp
  simp_rw [heq]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => ?_)]
  · congr 1
    rw [Fintype.sum_prod_type]
    simpa only [Prod.ext_iff] using posteriorPairDensity_merge label (p x) b.1 b.2
  · split_ifs
    · exact posteriorPairDensity_nonneg (hp x) _ _
    · exact le_rfl

end IndexedLaw

end Submission.Obl.k4_clean_cover_graph_atlas
