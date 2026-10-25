import Submission.Lib.K4ScalarCoreAssembly.ConditionalPairWitnesses
import Submission.Lib.K4ScalarActualSwitching.GridPalette
import Submission.Lib.K4ScalarActualSwitching.StarSelection

namespace Submission.Obl.k4_conditional_common_affine_field

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Submission.Lib.K4ScalarSwitching
open Submission.Lib.K4ScalarActualSwitching
open Submission.Lib.K4ScalarCoreAssembly

/-- Two separated palette bins are compatible with a dense set of the original states.
Only the countable observation is resampled, so the original source space can be arbitrary.
The output keeps every original control at the selected states. -/
theorem exists_two_original_witness_codes
    {Ω Q V : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Q] [StandardBorelSpace Q] [Countable Q]
    [MeasurableSingletonClass Q] [Nonempty Q]
    [MeasurableSpace V] [StandardBorelSpace V] [Countable V]
    [MeasurableSingletonClass V] [Nonempty V]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : μ univ ≠ 0)
    (A : Set Ω) (hA : MeasurableSet A) (hμA : ∀ᵐ p ∂μ, p ∈ A)
    (state : Ω → Q) (hstate : Measurable state)
    (code : Ω → V) (hcode : Measurable code)
    (center : V → ℝ) (hcenter : Measurable center)
    (π : Measure V) [IsProbabilityMeasure π]
    (K r : ℝ) (p : ℝ≥0∞) (hK : 0 < K)
    (hthin : ∀ x : ℝ, π.map center {v | |v - x| < r} ≤ p)
    (hsmall : ENNReal.ofReal K * p ≤ 1 / 2)
    (hcap : ∀ q j, μ {ω | state ω = q ∧ code ω = j} ≤
      ENNReal.ofReal K * μ {ω | state ω = q} * π {j}) :
    ∃ j : V × V, r ≤ |center j.1 - center j.2| ∧
      ∃ W : Set Ω, MeasurableSet W ∧ W ⊆ A ∧
        ENNReal.ofReal (1 / (2 * K ^ 2)) * μ univ ≤ μ W ∧
        ∀ ω ∈ W, ∃ a ∈ A, ∃ b ∈ A,
          state a = state ω ∧ state b = state ω ∧ code a = j.1 ∧ code b = j.2 := by
  classical
  let obs : Ω → Q × V := fun ω => (state ω, code ω)
  have hobs : Measurable obs := hstate.prodMk hcode
  let ρ := μ.map obs
  let B : Set (Q × V) := obs '' A
  have hB : MeasurableSet B := (Set.to_countable _).measurableSet
  have hρB : ∀ᵐ z ∂ρ, z ∈ B := by
    apply (ae_map_iff hobs.aemeasurable hB).mpr
    filter_upwards [hμA] with ω hω
    exact ⟨ω, hω, rfl⟩
  have hρ : ρ univ ≠ 0 := by
    change μ.map obs univ ≠ 0
    rw [Measure.map_apply hobs MeasurableSet.univ, preimage_univ]
    exact hμ
  let κ := conditionalResampling ρ Prod.fst measurable_fst
  letI : IsMarkovKernel κ := conditionalResampling_markov ρ Prod.fst measurable_fst
  have hρcap (q : Q) (j : V) :
      ρ {z | z.1 = q ∧ z.2 = j} ≤
        ENNReal.ofReal K * ρ (Prod.fst ⁻¹' {q}) * π {j} := by
    change μ.map obs {z | z.1 = q ∧ z.2 = j} ≤
      ENNReal.ofReal K * μ.map obs (Prod.fst ⁻¹' {q}) * π {j}
    rw [Measure.map_apply hobs (Set.to_countable _).measurableSet,
      Measure.map_apply hobs ((measurableSet_singleton q).preimage measurable_fst)]
    exact hcap q j
  have hκcap : ∀ᵐ z ∂ρ, (κ z).map Prod.snd ≤ ENNReal.ofReal K • π :=
    conditionalResampling_palette_le_of_atoms ρ Prod.fst measurable_fst
      Prod.snd measurable_snd π (ENNReal.ofReal K) hρcap
  have hκsupport : ∀ᵐ z ∂ρ, ∀ᵐ z' ∂κ z, z' ∈ B ∧ z'.1 = z.1 := by
    have hInv : Kernel.Invariant κ ρ := conditionalResampling_invariant ρ Prod.fst measurable_fst
    have hdraw : ∀ᵐ z ∂ρ, ∀ᵐ z' ∂κ z, z' ∈ B := by
      apply Measure.ae_ae_of_ae_comp
      rw [hInv]
      exact hρB
    filter_upwards [hdraw, conditionalResampling_ae_key ρ Prod.fst measurable_fst]
      with z hz hk
    exact hz.and hk
  let R : Set (V × V) := {j | r ≤ |center j.1 - center j.2|}
  have hbad : ∀ᵐ z ∂ρ,
      ((κ z).prod (κ z)) {ab | (ab.1.2, ab.2.2) ∉ R} ≤ 1 / 2 := by
    filter_upwards [hκcap] with z hz
    have hmap := Measure.map_mono hz hcenter
    rw [Measure.map_smul _ hcenter.aemeasurable,
      Measure.map_map hcenter measurable_snd] at hmap
    have hpair := pair_pencil_mass_le (κ z) (center ∘ Prod.snd)
      (hcenter.comp measurable_snd) (π.map center) (ENNReal.ofReal K) p r hmap hthin
    apply (le_trans ?_ hpair).trans hsmall
    apply measure_mono
    intro ab hab
    change ¬ r ≤ |center ab.1.2 - center ab.2.2| at hab
    exact lt_of_not_ge hab
  obtain ⟨j, hj, T, hTm, hTB, hTmass, hTwit⟩ :=
    exists_original_state_pair_witnesses ρ hρ B hB hρB Prod.fst measurable_fst
      Prod.snd measurable_snd κ π K hK R hκsupport hκcap hbad
  let W := A ∩ obs ⁻¹' T
  have hmass : μ W = ρ T := by
    change μ W = μ.map obs T
    rw [Measure.map_apply hobs hTm]
    apply measure_congr
    filter_upwards [hμA] with ω hω
    simp only [W, mem_inter_iff, hω, true_and]
  refine ⟨j, hj, W, hA.inter (hTm.preimage hobs), inter_subset_left, ?_, ?_⟩
  · simpa only [hmass, ρ, Measure.map_apply_of_aemeasurable hobs.aemeasurable
      MeasurableSet.univ, preimage_univ] using hTmass
  · intro ω hω
    obtain ⟨a', ha', b', hb', ha, hb, hca, hcb⟩ := hTwit (obs ω) hω.2
    obtain ⟨a, haA, rfl⟩ := ha'
    obtain ⟨b, hbA, rfl⟩ := hb'
    exact ⟨a, haA, b, hbA, ha, hb, hca, hcb⟩

end Submission.Obl.k4_conditional_common_affine_field
