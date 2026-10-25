/- Adapted within this LOT tree from o120/x0402, commit 70956fccdfd7e9924a3fa094355c65a03c16ee9c,
Submission/Obl/k4_unbounded_width_exclusion/PosteriorPair.lean. -/
import Mathlib

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Finset Filter

variable {X β : Type*} [MeasurableSpace X] [Fintype β]
  [MeasurableSpace β]

/-- The unnormalized joint law of an observation and its finite output
label, written using posterior weights. -/
def posteriorColorLaw (μ : Measure X) (π : X → β → ENNReal) : Measure (β × X) :=
  ∑ b, (μ.withDensity (fun x => π x b)).map (fun x => (b, x))

/-- Two posterior draws share one observation; the observation law is
kept unnormalized. -/
def posteriorPairLaw (μ : Measure X) (π : X → β → ENNReal) :
    Measure ((β × β) × X) :=
  ∑ b, ∑ b', (μ.withDensity (fun x => π x b * π x b')).map (fun x => ((b, b'), x))

omit [MeasurableSpace β] in
theorem withDensity_finite_sum (μ : Measure X) (f : β → X → ENNReal)
    (hf : ∀ b, Measurable (f b)) :
    μ.withDensity (fun x => ∑ b, f b x) = ∑ b, μ.withDensity (f b) := by
  ext E hE
  simp only [withDensity_apply _ hE, Measure.finsetSum_apply]
  exact lintegral_finsetSum _ (fun b _ => hf b)

theorem posteriorPairLaw_first (μ : Measure X) (π : X → β → ENNReal)
    (hπ : ∀ b, Measurable (fun x => π x b))
    (hmass : ∀ᵐ x ∂μ, ∑ b, π x b = 1) :
    (posteriorPairLaw μ π).map (fun p => (p.1.1, p.2)) = posteriorColorLaw μ π := by
  have hfirst : Measurable (fun p : (β × β) × X => (p.1.1, p.2)) := by fun_prop
  unfold posteriorPairLaw posteriorColorLaw
  rw [Measure.map_finset_sum' hfirst.aemeasurable]
  apply Finset.sum_congr rfl
  intro b _
  rw [Measure.map_finset_sum' hfirst.aemeasurable]
  have hmap (b' : β) :
      ((μ.withDensity (fun x => π x b * π x b')).map (fun x => ((b, b'), x))).map
        (fun p => (p.1.1, p.2)) =
      (μ.withDensity (fun x => π x b * π x b')).map (fun x => (b, x)) := by
    rw [Measure.map_map hfirst (by fun_prop)]
    rfl
  simp_rw [hmap]
  rw [← Measure.map_finset_sum' (by fun_prop :
    Measurable (fun x : X => (b, x))).aemeasurable]
  congr 1
  rw [← withDensity_finite_sum μ (fun b' x => π x b * π x b')
    (fun b' => (hπ b).mul (hπ b'))]
  apply withDensity_congr_ae
  filter_upwards [hmass] with x hx
  rw [← Finset.mul_sum, hx, mul_one]

theorem posteriorPairLaw_swap (μ : Measure X) (π : X → β → ENNReal) :
    (posteriorPairLaw μ π).map (fun p => ((p.1.2, p.1.1), p.2)) = posteriorPairLaw μ π := by
  have hswap : Measurable (fun p : (β × β) × X => ((p.1.2, p.1.1), p.2)) := by fun_prop
  unfold posteriorPairLaw
  simp_rw [Measure.map_finset_sum' hswap.aemeasurable]
  have hmap (b b' : β) :
      ((μ.withDensity (fun x => π x b * π x b')).map (fun x => ((b, b'), x))).map
        (fun p => ((p.1.2, p.1.1), p.2)) =
      (μ.withDensity (fun x => π x b * π x b')).map (fun x => ((b', b), x)) := by
    rw [Measure.map_map hswap (by fun_prop)]
    rfl
  simp_rw [hmap]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro b' _
  congr 1
  congr 1
  funext x
  exact mul_comm _ _

theorem posteriorPairLaw_second (μ : Measure X) (π : X → β → ENNReal)
    (hπ : ∀ b, Measurable (fun x => π x b))
    (hmass : ∀ᵐ x ∂μ, ∑ b, π x b = 1) :
    (posteriorPairLaw μ π).map (fun p => (p.1.2, p.2)) = posteriorColorLaw μ π := by
  calc
    _ = ((posteriorPairLaw μ π).map (fun p => ((p.1.2, p.1.1), p.2))).map
        (fun p => (p.1.1, p.2)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by rw [posteriorPairLaw_swap, posteriorPairLaw_first μ π hπ hmass]

theorem posteriorColorLaw_observation (μ : Measure X) (π : X → β → ENNReal)
    (hπ : ∀ b, Measurable (fun x => π x b))
    (hmass : ∀ᵐ x ∂μ, ∑ b, π x b = 1) :
    (posteriorColorLaw μ π).map Prod.snd = μ := by
  unfold posteriorColorLaw
  rw [Measure.map_finset_sum' measurable_snd.aemeasurable]
  have hmap (b : β) :
      ((μ.withDensity (fun x => π x b)).map (fun x => (b, x))).map Prod.snd =
        μ.withDensity (fun x => π x b) := by
    rw [Measure.map_map measurable_snd (by fun_prop)]
    exact Measure.map_id
  simp_rw [hmap]
  rw [← withDensity_finite_sum μ (fun b x => π x b) hπ]
  calc
    _ = μ.withDensity 1 := withDensity_congr_ae hmass
    _ = _ := withDensity_one

theorem posteriorPairLaw_observation (μ : Measure X) (π : X → β → ENNReal)
    (hπ : ∀ b, Measurable (fun x => π x b))
    (hmass : ∀ᵐ x ∂μ, ∑ b, π x b = 1) :
    (posteriorPairLaw μ π).map Prod.snd = μ := by
  calc
    _ = ((posteriorPairLaw μ π).map (fun p => (p.1.1, p.2))).map Prod.snd := by
      rw [Measure.map_map measurable_snd (by fun_prop)]
      rfl
    _ = _ := by rw [posteriorPairLaw_first μ π hπ hmass, posteriorColorLaw_observation μ π hπ hmass]

theorem posteriorPairLaw_total_mass (μ : Measure X) (π : X → β → ENNReal)
    (hπ : ∀ b, Measurable (fun x => π x b))
    (hmass : ∀ᵐ x ∂μ, ∑ b, π x b = 1) :
    posteriorPairLaw μ π Set.univ = μ Set.univ := by
  have h := congrArg (fun ν : Measure X => ν Set.univ) (posteriorPairLaw_observation μ π hπ hmass)
  simpa only [Measure.map_apply measurable_snd MeasurableSet.univ, Set.preimage_univ] using h

/-- Finite observed component measures determine posterior weights with
respect to their unnormalized sum. -/
def componentPosterior (ρ : β → Measure X) : X → β → ENNReal :=
  fun x b => (ρ b).rnDeriv (∑ b', ρ b') x

omit [MeasurableSpace β] in
theorem componentPosterior_measurable (ρ : β → Measure X) (b : β) :
    Measurable (fun x => componentPosterior ρ x b) :=
  (ρ b).measurable_rnDeriv _

omit [MeasurableSpace β] in
theorem componentPosterior_density (ρ : β → Measure X) [∀ b, IsFiniteMeasure (ρ b)] (b : β) :
    (∑ b', ρ b').withDensity (fun x => componentPosterior ρ x b) = ρ b := by
  have hle : ρ b ≤ ∑ b', ρ b' :=
    Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ b)
  exact Measure.withDensity_rnDeriv_eq _ _ hle.absolutelyContinuous

omit [MeasurableSpace β] in
theorem componentPosterior_mass (ρ : β → Measure X) [∀ b, IsFiniteMeasure (ρ b)] :
    ∀ᵐ x ∂(∑ b, ρ b), ∑ b, componentPosterior ρ x b = 1 := by
  have hmeas : Measurable (fun x => ∑ b, componentPosterior ρ x b) := by
    apply Finset.measurable_sum
    exact fun b _ => componentPosterior_measurable ρ b
  apply (withDensity_eq_iff_of_sigmaFinite hmeas.aemeasurable measurable_const.aemeasurable).mp
  calc
    _ = ∑ b, (∑ b', ρ b').withDensity (fun x => componentPosterior ρ x b) :=
      withDensity_finite_sum _ _ (componentPosterior_measurable ρ)
    _ = ∑ b, ρ b := Finset.sum_congr rfl (fun b _ => componentPosterior_density ρ b)
    _ = _ := withDensity_one.symm

theorem componentPosteriorPair_first (ρ : β → Measure X) [∀ b, IsFiniteMeasure (ρ b)] :
    (posteriorPairLaw (∑ b, ρ b) (componentPosterior ρ)).map (fun p => (p.1.1, p.2)) =
      ∑ b, (ρ b).map (fun x => (b, x)) := by
  rw [posteriorPairLaw_first _ _ (componentPosterior_measurable ρ) (componentPosterior_mass ρ)]
  unfold posteriorColorLaw
  apply Finset.sum_congr rfl
  intro b _
  rw [componentPosterior_density]

theorem componentPosteriorPair_second (ρ : β → Measure X) [∀ b, IsFiniteMeasure (ρ b)] :
    (posteriorPairLaw (∑ b, ρ b) (componentPosterior ρ)).map (fun p => (p.1.2, p.2)) =
      ∑ b, (ρ b).map (fun x => (b, x)) := by
  rw [posteriorPairLaw_second _ _ (componentPosterior_measurable ρ) (componentPosterior_mass ρ)]
  unfold posteriorColorLaw
  apply Finset.sum_congr rfl
  intro b _
  rw [componentPosterior_density]

theorem componentPosteriorPair_total_mass (ρ : β → Measure X) [∀ b, IsFiniteMeasure (ρ b)] :
    posteriorPairLaw (∑ b, ρ b) (componentPosterior ρ) Set.univ = ∑ b, ρ b Set.univ := by
  rw [posteriorPairLaw_total_mass _ _ (componentPosterior_measurable ρ) (componentPosterior_mass ρ)]
  exact Measure.finsetSum_apply _ _ _

variable [MeasurableSingletonClass β]

theorem posteriorColorLaw_component (μ : Measure X) (π : X → β → ENNReal)
    (b : β) {E : Set X} (hE : MeasurableSet E) :
    posteriorColorLaw μ π {p | p.1 = b ∧ p.2 ∈ E} =
      μ.withDensity (fun x => π x b) E := by
  classical
  have htag : MeasurableSet {p : β × X | p.1 = b ∧ p.2 ∈ E} := by
    exact (measurable_fst (measurableSet_singleton b)).inter (measurable_snd hE)
  unfold posteriorColorLaw
  rw [Measure.finsetSum_apply]
  have hmap (a : β) :
      ((μ.withDensity (fun x => π x a)).map (fun x => (a, x)))
          {p | p.1 = b ∧ p.2 ∈ E} =
        if a = b then μ.withDensity (fun x => π x b) E else 0 := by
    rw [Measure.map_apply (by fun_prop) htag]
    by_cases hab : a = b
    · subst a
      simp [Set.preimage_ofPred_eq]
    · simp [Set.preimage_ofPred_eq, hab]
  simp only [hmap]
  simp

theorem componentPosteriorPair_first_component (ρ : β → Measure X)
    [∀ b, IsFiniteMeasure (ρ b)] (b : β) {E : Set X} (hE : MeasurableSet E) :
    posteriorPairLaw (∑ a, ρ a) (componentPosterior ρ)
        {p | p.1.1 = b ∧ p.2 ∈ E} = ρ b E := by
  have htag : MeasurableSet {p : β × X | p.1 = b ∧ p.2 ∈ E} :=
    (measurable_fst (measurableSet_singleton b)).inter (measurable_snd hE)
  calc
    _ = ((posteriorPairLaw (∑ a, ρ a) (componentPosterior ρ)).map
        (fun p => (p.1.1, p.2))) {p | p.1 = b ∧ p.2 ∈ E} :=
      (Measure.map_apply (by fun_prop) htag).symm
    _ = _ := by
      rw [posteriorPairLaw_first _ _ (componentPosterior_measurable ρ) (componentPosterior_mass ρ),
        posteriorColorLaw_component _ _ b hE, componentPosterior_density]

theorem componentPosteriorPair_second_component (ρ : β → Measure X)
    [∀ b, IsFiniteMeasure (ρ b)] (b : β) {E : Set X} (hE : MeasurableSet E) :
    posteriorPairLaw (∑ a, ρ a) (componentPosterior ρ)
        {p | p.1.2 = b ∧ p.2 ∈ E} = ρ b E := by
  have htag : MeasurableSet {p : β × X | p.1 = b ∧ p.2 ∈ E} :=
    (measurable_fst (measurableSet_singleton b)).inter (measurable_snd hE)
  calc
    _ = ((posteriorPairLaw (∑ a, ρ a) (componentPosterior ρ)).map
        (fun p => (p.1.2, p.2))) {p | p.1 = b ∧ p.2 ∈ E} :=
      (Measure.map_apply (by fun_prop) htag).symm
    _ = _ := by
      rw [posteriorPairLaw_second _ _ (componentPosterior_measurable ρ) (componentPosterior_mass ρ),
        posteriorColorLaw_component _ _ b hE, componentPosterior_density]

end Submission.Obl.k4_fixed_budget_quadratic_recovery
