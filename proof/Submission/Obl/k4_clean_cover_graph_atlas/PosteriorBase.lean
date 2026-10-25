-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/PosteriorBase.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.PairLaw

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory Set Finset

variable {α X Y : Type*} [Fintype α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [MeasurableSpace X] [MeasurableSpace Y]

/-- Pair at the full original observation, then project to the comparison base. -/
noncomputable def posteriorBasePairLaw (ρ : Measure X) (p : X → α → ℝ)
    (base : X → Y) : Measure ((α × α) × Y) :=
  (posteriorPairLaw ρ p).map (fun q => (q.1, base q.2))

/-- Geometric support is inherited from positive original posterior components. -/
theorem posteriorBasePairLaw_ae (ρ : Measure X) (p : X → α → ℝ)
    (hpmeas : ∀ a, Measurable (fun x => p x a)) (hp : ∀ x a, 0 ≤ p x a)
    (base : X → Y) (hb : Measurable base)
    {P : (α × α) × Y → Prop} (hPm : MeasurableSet {q | P q})
    (hP : ∀ a b, ∀ᵐ x ∂ρ, 0 < p x a → 0 < p x b → P ((a, b), base x)) :
    ∀ᵐ q ∂posteriorBasePairLaw ρ p base, P q := by
  have hm : Measurable (fun q : (α × α) × X => (q.1, base q.2)) :=
    measurable_fst.prodMk (hb.comp measurable_snd)
  rw [posteriorBasePairLaw]
  apply (ae_map_iff hm.aemeasurable hPm).mpr
  exact posteriorPairLaw_ae ρ p hpmeas hp hP

theorem originalLabelLaw_component_base (ρ : Measure X) (p : X → α → ℝ)
    (base : X → Y) (hb : Measurable base) (a : α) (U : Set Y) (hU : MeasurableSet U) :
    originalLabelLaw ρ p {q | q.1 = a ∧ base q.2 ∈ U} =
      (ρ.withDensity (fun x => ENNReal.ofReal (p x a))).map base U := by
  classical
  have hE : MeasurableSet {q : α × X | q.1 = a ∧ base q.2 ∈ U} :=
    ((measurableSet_singleton a).preimage measurable_fst).inter
      (hU.preimage (hb.comp measurable_snd))
  rw [originalLabelLaw,
    Submission.Obl.k4_original_prior_line_extraction.indexedLaw_apply ρ _ hE,
    Measure.map_apply hb hU, withDensity_apply _ (hU.preimage hb)]
  rw [sum_eq_single a]
  · simp only [mem_setOf_eq, eq_self_iff_true, true_and, Set.preimage]
  · intro b _ hba
    simp [hba]
  · simp

/-- Projected posterior pairs keep the first original component base law exactly. -/
theorem posteriorBasePairLaw_first_component (ρ : Measure X) (p : X → α → ℝ)
    (hpmeas : ∀ a, Measurable (fun x => p x a)) (hp : ∀ x a, 0 ≤ p x a)
    (base : X → Y) (hb : Measurable base) (a : α) (U : Set Y) (hU : MeasurableSet U) :
    posteriorBasePairLaw ρ p base {q | q.1.1 = a ∧ q.2 ∈ U} =
      (ρ.withDensity (fun x => ENNReal.ofReal (p x a))).map base U := by
  have hE : MeasurableSet {q : (α × α) × Y | q.1.1 = a ∧ q.2 ∈ U} :=
    ((measurableSet_singleton a).preimage (measurable_fst.comp measurable_fst)).inter
      (hU.preimage measurable_snd)
  have hF : MeasurableSet {q : α × X | q.1 = a ∧ base q.2 ∈ U} :=
    ((measurableSet_singleton a).preimage measurable_fst).inter
      (hU.preimage (hb.comp measurable_snd))
  have heq := congrArg (fun μ : Measure (α × X) => μ {q | q.1 = a ∧ base q.2 ∈ U})
    (posteriorPairLaw_first_marginal ρ p hpmeas hp)
  have hm : Measurable (fun q : (α × α) × X => (q.1.1, q.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hb' : Measurable (fun q : (α × α) × X => (q.1, base q.2)) :=
    measurable_fst.prodMk (hb.comp measurable_snd)
  rw [Measure.map_apply hm hF] at heq
  rw [posteriorBasePairLaw, Measure.map_apply hb' hE]
  exact heq.trans (originalLabelLaw_component_base ρ p base hb a U hU)

/-- The second projected marginal is the same unchanged original component law. -/
theorem posteriorBasePairLaw_second_component (ρ : Measure X) (p : X → α → ℝ)
    (hpmeas : ∀ a, Measurable (fun x => p x a)) (hp : ∀ x a, 0 ≤ p x a)
    (base : X → Y) (hb : Measurable base) (a : α) (U : Set Y) (hU : MeasurableSet U) :
    posteriorBasePairLaw ρ p base {q | q.1.2 = a ∧ q.2 ∈ U} =
      (ρ.withDensity (fun x => ENNReal.ofReal (p x a))).map base U := by
  have hE : MeasurableSet {q : (α × α) × Y | q.1.2 = a ∧ q.2 ∈ U} :=
    ((measurableSet_singleton a).preimage (measurable_snd.comp measurable_fst)).inter
      (hU.preimage measurable_snd)
  have hF : MeasurableSet {q : α × X | q.1 = a ∧ base q.2 ∈ U} :=
    ((measurableSet_singleton a).preimage measurable_fst).inter
      (hU.preimage (hb.comp measurable_snd))
  have heq := congrArg (fun μ : Measure (α × X) => μ {q | q.1 = a ∧ base q.2 ∈ U})
    (posteriorPairLaw_second_marginal ρ p hpmeas hp)
  have hm : Measurable (fun q : (α × α) × X => (q.1.2, q.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hb' : Measurable (fun q : (α × α) × X => (q.1, base q.2)) :=
    measurable_fst.prodMk (hb.comp measurable_snd)
  rw [Measure.map_apply hm hF] at heq
  rw [posteriorBasePairLaw, Measure.map_apply hb' hE]
  exact heq.trans (originalLabelLaw_component_base ρ p base hb a U hU)

/-- Every event depending only on the paired labels has its original mass. -/
theorem posteriorBasePairLaw_indices (ρ : Measure X) (p : X → α → ℝ)
    (base : X → Y) (hb : Measurable base) (P : α × α → Prop) :
    posteriorBasePairLaw ρ p base {q | P q.1} = posteriorPairLaw ρ p {q | P q.1} := by
  have hm : Measurable (fun q : (α × α) × X => (q.1, base q.2)) :=
    measurable_fst.prodMk (hb.comp measurable_snd)
  have hE : MeasurableSet {q : (α × α) × Y | P q.1} :=
    (Set.to_countable {a : α × α | P a}).measurableSet.preimage measurable_fst
  rw [posteriorBasePairLaw, Measure.map_apply hm hE]
  rfl

/-- Projection after posterior pairing preserves the original total covered mass. -/
theorem posteriorBasePairLaw_univ (ρ : Measure X) (p : X → α → ℝ)
    (hpmeas : ∀ a, Measurable (fun x => p x a)) (hp : ∀ x a, 0 ≤ p x a)
    (base : X → Y) (hb : Measurable base) :
    posteriorBasePairLaw ρ p base univ =
      ∑ a, ρ.withDensity (fun x => ENNReal.ofReal (p x a)) univ := by
  have hm : Measurable (fun q : (α × α) × X => (q.1, base q.2)) :=
    measurable_fst.prodMk (hb.comp measurable_snd)
  rw [posteriorBasePairLaw,
    Measure.map_apply hm MeasurableSet.univ,
    preimage_univ, posteriorPairLaw_univ ρ p hpmeas hp, originalLabelLaw,
    Submission.Obl.k4_original_prior_line_extraction.indexedLaw_univ]
  apply sum_congr rfl
  intro a _
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]

end Submission.Obl.k4_clean_cover_graph_atlas
