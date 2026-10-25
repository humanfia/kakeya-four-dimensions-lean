-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/IncidenceRecovery.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/IncidenceRecovery.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.PairMerge
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.PosteriorRecovery

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory Set Finset
open Submission.Lib.K4OriginalLists

variable {α β X Z : Type*} [Fintype α] [Fintype β] [DecidableEq β]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace β] [MeasurableSingletonClass β]
  [MeasurableSpace X] [MeasurableSpace Z]

theorem originalLabelLaw_merge (ρ : Measure X) (p : X → α → ℝ)
    (hpmeas : ∀ a, Measurable (fun x => p x a)) (hp : ∀ x a, 0 ≤ p x a)
    (label : α → β) :
    (originalLabelLaw ρ p).map (fun q => (label q.1, q.2)) =
      originalLabelLaw ρ (fun x => mergedDensity label (p x)) := by
  classical
  rw [originalLabelLaw,
    indexedLaw_map_labels ρ _ (fun a => (hpmeas a).ennreal_ofReal) label]
  unfold originalLabelLaw
  congr 1
  funext b x
  unfold mergedDensity
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply sum_congr rfl
    intro a _
    split_ifs <;> simp
  · intro a _
    split_ifs <;> first | exact hp x a | exact le_rfl

/-- Indexed list success is precisely the sum of success events under the
unnormalized original incidence laws. -/
theorem original_observation_list_mass (ρ : Measure X) (p : X → α → ℝ)
    (μ : α → Measure Z) (O : Z → X) (hO : Measurable O)
    (hlaw : ∀ a, ρ.withDensity (fun x => ENNReal.ofReal (p x a)) = (μ a).map O)
    (label : α → β) (L : X → Finset β) (hL : MeasurableLists L) :
    originalLabelLaw ρ p {q | label q.1 ∈ L q.2} =
      ∑ a, μ a {z | label a ∈ L (O z)} := by
  have hE : MeasurableSet {q : α × X | label q.1 ∈ L q.2} := by
    have hU : MeasurableSet (⋃ a : α, ({a} : Set α) ×ˢ {x | label a ∈ L x}) :=
      MeasurableSet.iUnion fun a => (measurableSet_singleton a).prod (hL (label a))
    convert hU using 1
    ext q
    simp
  rw [originalLabelLaw,
    Submission.Obl.k4_original_prior_line_extraction.indexedLaw_apply ρ _ hE]
  apply sum_congr rfl
  intro a _
  change (∫⁻ x in {x | label a ∈ L x}, ENNReal.ofReal (p x a) ∂ρ) = _
  rw [← withDensity_apply _ (hL (label a)), hlaw a,
    Measure.map_apply hO (hL (label a))]
  rfl

/-- Merge all candidate jet labels before maximizing lists. Neighbor agreement
under the original posterior pair law becomes the same success floor under the
original component incidence laws, with no loss depending on the number of labels. -/
theorem recover_original_incidence_lists (ρ : Measure X) (p : X → α → ℝ)
    (hpmeas : ∀ a, Measurable (fun x => p x a))
    (hpint : ∀ a, Integrable (fun x => p x a) ρ) (hp : ∀ x a, 0 ≤ p x a)
    (μ : α → Measure Z) (O : Z → X) (hO : Measurable O)
    (hlaw : ∀ a, ρ.withDensity (fun x => ENNReal.ofReal (p x a)) = (μ a).map O)
    (label : α → β) (neighbors : β → Finset β) (D : ℕ)
    (hcard : ∀ b, (neighbors b).card ≤ D)
    (mass : ℝ) (hpair : ENNReal.ofReal mass ≤
      posteriorPairLaw ρ p {q | label q.1.2 ∈ neighbors (label q.1.1)}) :
    ∃ L : X → Finset β, MeasurableLists L ∧ (∀ x, (L x).card ≤ D) ∧
      ENNReal.ofReal mass ≤ ∑ a, μ a {z | label a ∈ L (O z)} := by
  classical
  let q : X → β → ℝ := fun x => mergedDensity label (p x)
  have hqm (b : β) : Measurable (fun x => q x b) := by
    unfold q mergedDensity
    apply Finset.measurable_sum
    intro a _
    split_ifs <;> first | exact hpmeas a | exact measurable_const
  have hqi (b : β) : Integrable (fun x => q x b) ρ := by
    unfold q mergedDensity
    apply integrable_finsetSum
    intro a _
    split_ifs <;> first | exact hpint a | exact integrable_zero X ℝ ρ
  have hqn (x : X) (b : β) : 0 ≤ q x b := mergedDensity_nonneg label (hp x) b
  have hmap : Measurable (fun z : (α × α) × X => ((label z.1.1, label z.1.2), z.2)) :=
    (((measurable_of_countable label).comp (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_of_countable label).comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd
  have hE : MeasurableSet {z : (β × β) × X | z.1.2 ∈ neighbors z.1.1} :=
    (Set.to_countable {b : β × β | b.2 ∈ neighbors b.1}).measurableSet.preimage measurable_fst
  have hpair' : ENNReal.ofReal mass ≤ posteriorPairLaw ρ q {z | z.1.2 ∈ neighbors z.1.1} := by
    rw [← posteriorPairLaw_merge ρ p hpmeas hp label, Measure.map_apply hmap hE]
    exact hpair
  obtain ⟨L, hL, hLc, hsuccess⟩ :=
    recover_original_pair_agreement ρ q hqm hqi hqn neighbors D hcard mass hpair'
  refine ⟨L, hL, hLc, ?_⟩
  have hmap' : Measurable (fun z : α × X => (label z.1, z.2)) :=
    ((measurable_of_countable label).comp measurable_fst).prodMk measurable_snd
  rw [← originalLabelLaw_merge ρ p hpmeas hp label,
    Measure.map_apply hmap' (measurableSet_list_success L hL)] at hsuccess
  exact hsuccess.trans_eq (original_observation_list_mass ρ p μ O hO hlaw label L hL)

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
