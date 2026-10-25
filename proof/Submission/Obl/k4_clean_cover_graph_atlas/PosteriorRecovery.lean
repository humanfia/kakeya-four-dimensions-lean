-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/PosteriorRecovery.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.PairLaw
import Submission.Lib.K4MeshListRecovery.PosteriorLists

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory Set Finset
open Submission.Lib.K4OriginalLists

variable {α X : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace X]

noncomputable def neighborScore (p : α → ℝ) (neighbors : α → Finset α) : ℝ :=
  (∑ b, p b * ∑ a ∈ neighbors b, p a) / ∑ a, p a

lemma neighborScore_nonneg {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (neighbors : α → Finset α) :
    0 ≤ neighborScore p neighbors := by
  exact div_nonneg (sum_nonneg fun b _ => mul_nonneg (hp b)
    (sum_nonneg fun a _ => hp a)) (sum_nonneg fun a _ => hp a)

lemma neighborScore_le_total {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (neighbors : α → Finset α) :
    neighborScore p neighbors ≤ ∑ a, p a := by
  classical
  by_cases hz : ∑ a, p a = 0
  · simp [neighborScore, hz]
  · have hpos : 0 < ∑ a, p a :=
      lt_of_le_of_ne (sum_nonneg fun a _ => hp a) (Ne.symm hz)
    apply (div_le_iff₀ hpos).mpr
    calc
      _ ≤ ∑ b, p b * ∑ a, p a := sum_le_sum fun b _ =>
        mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg (subset_univ (neighbors b)) (fun a _ _ => hp a)) (hp b)
      _ = _ := (sum_mul ..).symm

lemma neighborScore_eq_sum_pair (p : α → ℝ) (neighbors : α → Finset α) :
    neighborScore p neighbors = ∑ b, ∑ a ∈ neighbors b, posteriorPairDensity p b a := by
  simp only [neighborScore, posteriorPairDensity, ← sum_div, ← mul_sum]

lemma integrable_neighborScore (μ : Measure X) (p : X → α → ℝ)
    (hpmeas : ∀ a, Measurable (fun x => p x a))
    (hpint : ∀ a, Integrable (fun x => p x a) μ) (hp : ∀ x a, 0 ≤ p x a)
    (neighbors : α → Finset α) : Integrable (fun x => neighborScore (p x) neighbors) μ := by
  have ht : Integrable (fun x => ∑ a, p x a) μ := integrable_finsetSum _ (fun a _ => hpint a)
  have hm : Measurable (fun x => neighborScore (p x) neighbors) := by
    unfold neighborScore
    fun_prop
  apply ht.mono' hm.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (neighborScore_nonneg (hp x) neighbors)]
  exact neighborScore_le_total (hp x) neighbors

/-- The mass of neighboring posterior pairs is the usual posterior-neighbor integral,
with no normalization of the covered law. -/
theorem posteriorPairLaw_neighbor_mass (μ : Measure X) (p : X → α → ℝ)
    (hpmeas : ∀ a, Measurable (fun x => p x a))
    (hpint : ∀ a, Integrable (fun x => p x a) μ) (hp : ∀ x a, 0 ≤ p x a)
    (neighbors : α → Finset α) :
    posteriorPairLaw μ p {q | q.1.2 ∈ neighbors q.1.1} =
      ENNReal.ofReal (∫ x, neighborScore (p x) neighbors ∂μ) := by
  classical
  have hE : MeasurableSet {q : (α × α) × X | q.1.2 ∈ neighbors q.1.1} :=
    (Set.toFinite {a : α × α | a.2 ∈ neighbors a.1}).measurableSet.preimage measurable_fst
  have hd (a b : α) : Measurable (fun x =>
      ENNReal.ofReal (posteriorPairDensity (p x) a b)) := by
    unfold posteriorPairDensity
    fun_prop
  have hcomp (a b : α) :
      (∫⁻ x in {x : X | b ∈ neighbors a},
        ENNReal.ofReal (posteriorPairDensity (p x) a b) ∂μ) =
      if b ∈ neighbors a then ∫⁻ x, ENNReal.ofReal (posteriorPairDensity (p x) a b) ∂μ else 0 := by
    by_cases h : b ∈ neighbors a <;> simp [h]
  calc
    _ = ∑ a, ∑ b ∈ neighbors a,
        ∫⁻ x, ENNReal.ofReal (posteriorPairDensity (p x) a b) ∂μ := by
      rw [posteriorPairLaw,
        Submission.Obl.k4_original_prior_line_extraction.indexedLaw_apply μ _ hE,
        Fintype.sum_prod_type]
      apply sum_congr rfl
      intro a _
      change (∑ b, ∫⁻ x in {x : X | b ∈ neighbors a},
        ENNReal.ofReal (posteriorPairDensity (p x) a b) ∂μ) = _
      simp_rw [hcomp]
      conv_rhs => rw [show neighbors a = univ.filter (fun b => b ∈ neighbors a) by ext; simp]
      rw [sum_filter]
    _ = ∫⁻ x, ∑ a, ∑ b ∈ neighbors a, ENNReal.ofReal (posteriorPairDensity (p x) a b) ∂μ := by
      rw [lintegral_finsetSum univ (fun a _ => Finset.measurable_sum _ (fun b _ => hd a b))]
      apply sum_congr rfl
      intro a _
      exact (lintegral_finsetSum (neighbors a) (fun b _ => hd a b)).symm
    _ = ∫⁻ x, ENNReal.ofReal (neighborScore (p x) neighbors) ∂μ := by
      apply lintegral_congr
      intro x
      rw [neighborScore_eq_sum_pair,
        ENNReal.ofReal_sum_of_nonneg (fun a _ => sum_nonneg fun b _ =>
          posteriorPairDensity_nonneg (hp x) a b)]
      apply sum_congr rfl
      intro a _
      exact (ENNReal.ofReal_sum_of_nonneg (fun b _ => posteriorPairDensity_nonneg (hp x) a b)).symm
    _ = _ := (ofReal_integral_eq_lintegral_ofReal (integrable_neighborScore μ p hpmeas hpint hp neighbors)
      (Filter.Eventually.of_forall fun x => neighborScore_nonneg (hp x) neighbors)).symm

/-- A measurable list policy defines a measurable event in the indexed original law. -/
theorem measurableSet_list_success (L : X → Finset α) (hL : MeasurableLists L) :
    MeasurableSet {q : α × X | q.1 ∈ L q.2} := by
  have hU : MeasurableSet (⋃ a : α, ({a} : Set α) ×ˢ {x | a ∈ L x}) :=
    MeasurableSet.iUnion fun a => (measurableSet_singleton a).prod (hL a)
  convert hU using 1
  ext q
  simp

/-- The list-density integral is exactly the original indexed law's success mass. -/
theorem originalLabelLaw_list_mass (μ : Measure X) (p : X → α → ℝ)
    (hpmeas : ∀ a, Measurable (fun x => p x a))
    (hpint : ∀ a, Integrable (fun x => p x a) μ) (hp : ∀ x a, 0 ≤ p x a)
    (L : X → Finset α) (hL : MeasurableLists L) :
    originalLabelLaw μ p {q | q.1 ∈ L q.2} =
      ENNReal.ofReal (∫ x, ∑ a ∈ L x, p x a ∂μ) := by
  classical
  have hi (a : α) : Measurable ({x | a ∈ L x}.indicator (fun x => ENNReal.ofReal (p x a))) :=
    (hpmeas a).ennreal_ofReal.indicator (hL a)
  have hpoint (x : X) :
      (∑ a, {x | a ∈ L x}.indicator (fun x => ENNReal.ofReal (p x a)) x) =
        ENNReal.ofReal (∑ a ∈ L x, p x a) := by
    calc
      _ = ∑ a ∈ L x, ENNReal.ofReal (p x a) := by
        conv_rhs => rw [show L x = univ.filter (fun a => a ∈ L x) by ext; simp]
        rw [sum_filter]
        apply sum_congr rfl
        intro a _
        by_cases ha : a ∈ L x <;> simp [ha]
      _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun a _ => hp x a)).symm
  calc
    _ = ∑ a, ∫⁻ x in {x | a ∈ L x}, ENNReal.ofReal (p x a) ∂μ := by
      rw [originalLabelLaw,
        Submission.Obl.k4_original_prior_line_extraction.indexedLaw_apply μ _
          (measurableSet_list_success L hL)]
      rfl
    _ = ∑ a, ∫⁻ x, {x | a ∈ L x}.indicator (fun x => ENNReal.ofReal (p x a)) x ∂μ := by
      apply sum_congr rfl
      intro a _
      exact (lintegral_indicator (hL a) _).symm
    _ = ∫⁻ x, ENNReal.ofReal (∑ a ∈ L x, p x a) ∂μ := by
      rw [← lintegral_finsetSum univ (fun a _ => hi a)]
      simp_rw [hpoint]
    _ = _ := (ofReal_integral_eq_lintegral_ofReal (integrable_listDensity μ p L hpint hL)
      (Filter.Eventually.of_forall fun x => sum_nonneg fun a _ => hp x a)).symm

/-- Posterior agreement yields bounded measurable original-observation lists with the
same aggregate success lower bound. -/
theorem recover_original_pair_agreement (μ : Measure X) (p : X → α → ℝ)
    (hpmeas : ∀ a, Measurable (fun x => p x a))
    (hpint : ∀ a, Integrable (fun x => p x a) μ) (hp : ∀ x a, 0 ≤ p x a)
    (neighbors : α → Finset α) (D : ℕ) (hcard : ∀ a, (neighbors a).card ≤ D)
    (mass : ℝ) (hpair : ENNReal.ofReal mass ≤
      posteriorPairLaw μ p {q | q.1.2 ∈ neighbors q.1.1}) :
    ∃ L : X → Finset α, MeasurableLists L ∧ (∀ x, (L x).card ≤ D) ∧
      ENNReal.ofReal mass ≤ originalLabelLaw μ p {q | q.1 ∈ L q.2} := by
  rw [posteriorPairLaw_neighbor_mass μ p hpmeas hpint hp neighbors] at hpair
  have hnn : 0 ≤ ∫ x, neighborScore (p x) neighbors ∂μ :=
    integral_nonneg fun x => neighborScore_nonneg (hp x) neighbors
  have hpair' : mass ≤ ∫ x, neighborScore (p x) neighbors ∂μ :=
    (ENNReal.ofReal_le_ofReal_iff hnn).mp hpair
  obtain ⟨L, hL, hLc, hsuccess⟩ :=
    Submission.Lib.K4MeshListRecovery.recover_neighbor_density_mass μ p hpmeas hpint hp
      univ D neighbors (fun a => ⟨subset_univ _, hcard a⟩) mass hpair'
  refine ⟨L, hL, fun x => (hLc x).2, ?_⟩
  rw [originalLabelLaw_list_mass μ p hpmeas hpint hp L hL]
  exact ENNReal.ofReal_le_ofReal hsuccess

end Submission.Obl.k4_clean_cover_graph_atlas
