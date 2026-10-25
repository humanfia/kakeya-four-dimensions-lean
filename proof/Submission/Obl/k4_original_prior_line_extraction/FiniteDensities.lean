import Mathlib
import ChallengeDeps
import Submission.Obl.k4_profile_density_bounds.Mass

set_option linter.unusedSectionVars false

namespace Submission.Obl.k4_original_prior_line_extraction

open MeasureTheory Set Filter
open scoped ENNReal

variable {A X : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype A] [MeasurableSpace X]

/-- The base law of one member of a finite indexed law. -/
noncomputable def component (μ : Measure (A × X)) (a : A) : Measure X :=
  (μ.restrict (Prod.fst ⁻¹' {a})).map Prod.snd

lemma component_apply (μ : Measure (A × X)) (a : A) {U : Set X}
    (hU : MeasurableSet U) : component μ a U = μ ({a} ×ˢ U) := by
  rw [component, Measure.map_apply measurable_snd hU,
    Measure.restrict_apply (hU.preimage measurable_snd)]
  congr 1
  ext p
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_prod]
  tauto

lemma measure_eq_sum_components (μ : Measure (A × X)) {E : Set (A × X)}
    (hE : MeasurableSet E) :
    μ E = ∑ a, component μ a {x | (a, x) ∈ E} := by
  have hsection (a : A) : MeasurableSet {x | (a, x) ∈ E} :=
    hE.preimage (measurable_const.prodMk measurable_id)
  have hdec : E = ⋃ a, ({a} : Set A) ×ˢ {x | (a, x) ∈ E} := by
    ext p
    simp
  have hd : Pairwise (Function.onFun Disjoint
      (fun a : A => ({a} : Set A) ×ˢ {x | (a, x) ∈ E})) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    rintro p ⟨ha, _⟩ ⟨hb, _⟩
    exact hab (by simpa using ha.symm.trans hb)
  calc
    μ E = ∑' a, μ (({a} : Set A) ×ˢ {x | (a, x) ∈ E}) := by
      conv_lhs => rw [hdec]
      exact measure_iUnion hd (fun a => (measurableSet_singleton a).prod (hsection a))
    _ = ∑ a, component μ a {x | (a, x) ∈ E} := by
      simp only [tsum_fintype, component_apply μ _ (hsection _)]

lemma measure_univ_eq_sum_components (μ : Measure (A × X)) :
    μ univ = ∑ a, component μ a univ := by
  simpa using measure_eq_sum_components μ MeasurableSet.univ

lemma exists_component_densities (μ : Measure (A × X)) [IsFiniteMeasure μ]
    (ρ : Measure X) [SigmaFinite ρ]
    (habs : ∀ a, component μ a ≪ ρ) :
    ∃ f : A → X → ℝ≥0∞, (∀ a, Measurable (f a)) ∧
      (∀ a, ρ.withDensity (f a) = component μ a) := by
  letI (a : A) : IsFiniteMeasure (component μ a) := by
    unfold component
    infer_instance
  refine ⟨fun a => (component μ a).rnDeriv ρ,
    fun a => Measure.measurable_rnDeriv _ _, fun a => ?_⟩
  exact Measure.withDensity_rnDeriv_eq _ _ (habs a)

lemma component_lintegral (μ : Measure (A × X)) (ρ : Measure X)
    {f : A → X → ℝ≥0∞} (hf : ∀ a, ρ.withDensity (f a) = component μ a)
    {U : Set X} (hU : MeasurableSet U) (a : A) :
    (∫⁻ x in U, f a x ∂ρ) = μ ({a} ×ˢ U) := by
  rw [← withDensity_apply _ hU, hf a, component_apply μ a hU]

lemma label_density_lintegral {I : Type*} [DecidableEq I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (μ : Measure (A × X)) (ρ : Measure X)
    {f : A → X → ℝ≥0∞} (hf : ∀ a, Measurable (f a))
    (hlaw : ∀ a, ρ.withDensity (f a) = component μ a)
    (ℓ : A → I) (i : I) {U : Set X} (hU : MeasurableSet U) :
    (∫⁻ x in U, ∑ a, if ℓ a = i then f a x else 0 ∂ρ) =
      μ {p | ℓ p.1 = i ∧ p.2 ∈ U} := by
  classical
  have hfun (a : A) : Measurable (fun x => if ℓ a = i then f a x else 0) := by
    split_ifs
    · exact hf a
    · exact measurable_const
  have hE : MeasurableSet {p : A × X | ℓ p.1 = i ∧ p.2 ∈ U} :=
    ((measurableSet_singleton i).preimage
      ((measurable_of_countable ℓ).comp measurable_fst)).inter
      (hU.preimage measurable_snd)
  rw [lintegral_finsetSum Finset.univ (fun a _ => hfun a),
    measure_eq_sum_components μ hE]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : ℓ a = i
  · simpa [ha] using
      (withDensity_apply (f a) hU).symm.trans (congrArg (fun ν => ν U) (hlaw a))
  · simp [ha]

lemma ae_label_density_le {I : Type*} [DecidableEq I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (μ : Measure (A × X)) (ρ : Measure X)
    [SigmaFinite ρ] {f : A → X → ℝ≥0∞} (hf : ∀ a, Measurable (f a))
    (hlaw : ∀ a, ρ.withDensity (f a) = component μ a)
    (ℓ : A → I) (i : I) (C : ℝ≥0∞)
    (hbound : ∀ U : Set X, MeasurableSet U →
      μ {p | ℓ p.1 = i ∧ p.2 ∈ U} ≤ C * ρ U) :
    ∀ᵐ x ∂ρ, (∑ a, if ℓ a = i then f a x else 0) ≤ C := by
  classical
  have hg : Measurable (fun x => ∑ a, if ℓ a = i then f a x else 0) := by
    apply Finset.measurable_sum
    intro a _
    split_ifs
    · exact hf a
    · exact measurable_const
  apply Submission.Obl.k4_profile_density_bounds.ae_density_le_of_measure_bound ρ hg C
  intro U hU
  rw [withDensity_apply _ hU, label_density_lintegral μ ρ hf hlaw ℓ i hU]
  exact hbound U hU

/-- Joint densities can be chosen with both original marginal ceilings everywhere.
Only one common null set is removed; neither index prior is conditioned. -/
lemma exists_pair_densities {I L : Type*}
    [MeasurableSpace I] [MeasurableSingletonClass I] [Fintype I]
    [MeasurableSpace L] [MeasurableSingletonClass L] [Fintype L]
    (μ : Measure ((I × L) × X)) [IsFiniteMeasure μ]
    (ρ : Measure X) [SigmaFinite ρ] (C₁ : I → ℝ≥0∞) (C₂ : L → ℝ≥0∞)
    (h₁ : ∀ i U, MeasurableSet U → μ {p | p.1.1 = i ∧ p.2 ∈ U} ≤ C₁ i * ρ U)
    (h₂ : ∀ j U, MeasurableSet U → μ {p | p.1.2 = j ∧ p.2 ∈ U} ≤ C₂ j * ρ U) :
    ∃ f : (I × L) → X → ℝ≥0∞,
      (∀ a, Measurable (f a)) ∧
      (∀ a, ρ.withDensity (f a) = component μ a) ∧
      (∀ x i, ∑ j, f (i, j) x ≤ C₁ i) ∧
      (∀ x j, ∑ i, f (i, j) x ≤ C₂ j) := by
  classical
  have habs (a : I × L) : component μ a ≪ ρ := by
    apply Measure.absolutelyContinuous_of_le_smul (c := C₁ a.1)
    apply Measure.le_iff.mpr
    intro U hU
    rw [component_apply μ a hU, Measure.smul_apply, smul_eq_mul]
    apply le_trans (measure_mono ?_) (h₁ a.1 U hU)
    rintro p ⟨ha, hx⟩
    exact ⟨congrArg Prod.fst ha, hx⟩
  obtain ⟨f, hf, hlaw⟩ := exists_component_densities μ ρ habs
  have hcap₁ (i : I) : ∀ᵐ x ∂ρ, ∑ j, f (i, j) x ≤ C₁ i := by
    simpa [Fintype.sum_prod_type, Finset.sum_comm] using
      ae_label_density_le μ ρ hf hlaw Prod.fst i (C₁ i) (h₁ i)
  have hcap₂ (j : L) : ∀ᵐ x ∂ρ, ∑ i, f (i, j) x ≤ C₂ j := by
    simpa [Fintype.sum_prod_type] using
      ae_label_density_le μ ρ hf hlaw Prod.snd j (C₂ j) (h₂ j)
  let G : Set X := {x | (∀ i, ∑ j, f (i, j) x ≤ C₁ i) ∧
    (∀ j, ∑ i, f (i, j) x ≤ C₂ j)}
  have hG : MeasurableSet G := by
    have heq₁ : {x : X | ∀ i, (∑ j, f (i, j) x) ≤ C₁ i} =
        ⋂ i, {x : X | (∑ j, f (i, j) x) ≤ C₁ i} := by ext x; simp
    have heq₂ : {x : X | ∀ j, (∑ i, f (i, j) x) ≤ C₂ j} =
        ⋂ j, {x : X | (∑ i, f (i, j) x) ≤ C₂ j} := by ext x; simp
    change MeasurableSet ({x : X | ∀ i, (∑ j, f (i, j) x) ≤ C₁ i} ∩
      {x : X | ∀ j, (∑ i, f (i, j) x) ≤ C₂ j})
    rw [heq₁, heq₂]
    exact (MeasurableSet.iInter fun i => measurableSet_le
      (Finset.measurable_sum Finset.univ fun j _ => hf (i, j)) (measurable_const (a := C₁ i))).inter
      (MeasurableSet.iInter fun j => measurableSet_le
      (Finset.measurable_sum Finset.univ fun i _ => hf (i, j)) (measurable_const (a := C₂ j)))
  have hGae : ∀ᵐ x ∂ρ, x ∈ G :=
    ((ae_all_iff.mpr hcap₁).and (ae_all_iff.mpr hcap₂))
  refine ⟨fun a => G.indicator (f a), fun a => (hf a).indicator hG, ?_, ?_, ?_⟩
  · intro a
    calc
      ρ.withDensity (G.indicator (f a)) = ρ.withDensity (f a) := by
        apply withDensity_congr_ae
        filter_upwards [hGae] with x hx
        exact indicator_of_mem hx _
      _ = component μ a := hlaw a
  · intro x i
    by_cases hx : x ∈ G
    · simpa only [indicator_of_mem hx] using hx.1 i
    · simp [indicator_of_notMem hx]
  · intro x j
    by_cases hx : x ∈ G
    · simpa only [indicator_of_mem hx] using hx.2 j
    · simp [indicator_of_notMem hx]

/-- Assemble all finite pair components without changing their indices. -/
noncomputable def indexedLaw (ρ : Measure X) (f : A → X → ℝ≥0∞) : Measure (A × X) :=
  ∑ a, (ρ.withDensity (f a)).map (Prod.mk a)

lemma indexedLaw_apply (ρ : Measure X) (f : A → X → ℝ≥0∞)
    {E : Set (A × X)} (hE : MeasurableSet E) :
    indexedLaw ρ f E = ∑ a, ∫⁻ x in {x | (a, x) ∈ E}, f a x ∂ρ := by
  classical
  simp only [indexedLaw, Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  have hm : Measurable (Prod.mk a : X → A × X) := measurable_const.prodMk measurable_id
  rw [Measure.map_apply hm hE, withDensity_apply _ (hE.preimage hm)]
  rfl

lemma indexedLaw_univ (ρ : Measure X) (f : A → X → ℝ≥0∞) :
    indexedLaw ρ f univ = ∑ a, ∫⁻ x, f a x ∂ρ := by
  simp [indexedLaw_apply ρ f MeasurableSet.univ]

lemma indexedLaw_label_bound {I : Type*} [DecidableEq I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (ρ : Measure X)
    (f : A → X → ℝ≥0∞) (hf : ∀ a, Measurable (f a))
    (ℓ : A → I) (i : I) (C : ℝ≥0∞)
    (hbound : ∀ x, (∑ a, if ℓ a = i then f a x else 0) ≤ C)
    {U : Set X} (hU : MeasurableSet U) :
    indexedLaw ρ f {p | ℓ p.1 = i ∧ p.2 ∈ U} ≤ C * ρ U := by
  classical
  have hE : MeasurableSet {p : A × X | ℓ p.1 = i ∧ p.2 ∈ U} :=
    ((measurableSet_singleton i).preimage
      ((measurable_of_countable ℓ).comp measurable_fst)).inter
      (hU.preimage measurable_snd)
  calc
    _ = ∫⁻ x in U, ∑ a, if ℓ a = i then f a x else 0 ∂ρ := by
      rw [indexedLaw_apply ρ f hE,
        lintegral_finsetSum Finset.univ (fun a _ => ?_)]
      · apply Finset.sum_congr rfl
        intro a _
        by_cases ha : ℓ a = i <;> simp [ha]
      · split_ifs
        · exact hf a
        · exact measurable_const
    _ ≤ ∫⁻ x in U, C ∂ρ := lintegral_mono (fun x => hbound x)
    _ = _ := setLIntegral_const U C

lemma indexedLaw_ae (ρ : Measure X) (f : A → X → ℝ≥0∞)
    (hf : ∀ a, Measurable (f a)) {P : A × X → Prop}
    (hP : ∀ a, ∀ᵐ x ∂ρ, f a x ≠ 0 → P (a, x)) :
    ∀ᵐ p ∂indexedLaw ρ f, P p := by
  unfold indexedLaw
  rw [ae_finsetSum_measure_iff]
  intro a _
  rw [(measurableEmbedding_prodMk_left a).ae_map_iff, ae_withDensity_iff (hf a)]
  exact hP a

end Submission.Obl.k4_original_prior_line_extraction
