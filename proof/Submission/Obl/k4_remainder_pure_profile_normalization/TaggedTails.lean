import Submission.Obl.k4_remainder_pure_profile_normalization.WorldMeasure
import Submission.Obl.k4_remainder_pure_profile_normalization.NormalizeSamples

namespace Submission.Obl.k4_remainder_pure_profile_normalization
open MeasureTheory Filter Set
open Submission.Obl.k4_native_grid_profile_extension.Profiles
open scoped ENNReal

def Data.TypicalAt (p : Data) (σ e : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → IsPowerSmall p.N (fun k => ∑ b, ENNReal.ofReal (p.ω k b) *
    p.incidenceMeasure k b {z |
      p.g k b σ (obs (p.B k b) (δ (p.N k) σ) z) < ENNReal.ofReal (p.N k ^ (-e - τ)) ∨
      ENNReal.ofReal (p.N k ^ (-e + τ)) < p.g k b σ (obs (p.B k b) (δ (p.N k) σ) z)})

def Data.UpperAt (p : Data) (σ e : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → IsPowerSmall p.N (fun k => ∑ b, ENNReal.ofReal (p.ω k b) *
    p.incidenceMeasure k b {z |
      ENNReal.ofReal (p.N k ^ (-e + τ)) < p.g k b σ (obs (p.B k b) (δ (p.N k) σ) z)})

theorem Data.sampleMeasure_univ (p : Data) (k : ℕ) :
    p.sampleMeasure k univ = ∑ b, ENNReal.ofReal (p.ω k b) * p.incidenceMeasure k b univ := by
  simpa only [preimage_univ] using p.sampleMeasure_apply k MeasurableSet.univ

theorem Data.measurable_sampledDensity_of (p : Data) (σ : ℝ)
    (hg : ∀ k b, Measurable (p.g k b σ)) (k : ℕ) : Measurable (p.sampledDensity σ k) := by
  apply measurable_from_prod_countable_right
  intro b
  change Measurable (fun z : Incidence => p.g k b σ (obs (p.B k b) (δ (p.N k) σ) z))
  exact (hg k b).comp
    (Submission.Obl.k4_native_grid_profile_extension.measurable_pureObservation _ _)

theorem Data.hasTypicalDensity_of_typicalAt (p : Data) {σ e : ℝ}
    (hg : ∀ k b, Measurable (p.g k b σ)) (ht : p.TypicalAt σ e) :
    HasTypicalDensity p.N p.sampleMeasure (p.sampledDensity σ) e := by
  intro τ hτ
  obtain ⟨c, hc, hb⟩ := ht τ hτ
  refine ⟨c, hc, ?_⟩
  filter_upwards [hb] with k hk
  have hm : MeasurableSet {x : p.SampleState k |
      p.sampledDensity σ k x < ENNReal.ofReal (p.N k ^ (-e - τ)) ∨
      ENNReal.ofReal (p.N k ^ (-e + τ)) < p.sampledDensity σ k x} :=
    (measurableSet_lt (p.measurable_sampledDensity_of σ hg k) measurable_const).union
      (measurableSet_lt measurable_const (p.measurable_sampledDensity_of σ hg k))
  rw [Data.sampleMeasure_apply p k hm]
  exact hk

theorem Data.tagged_upper_of_upperAt (p : Data) {σ e : ℝ}
    (hg : ∀ k b, Measurable (p.g k b σ)) (ht : p.UpperAt σ e) :
    ∀ τ : ℝ, 0 < τ → IsPowerSmall p.N (fun k => p.sampleMeasure k
      {z | ENNReal.ofReal (p.N k ^ (-e + τ)) < p.sampledDensity σ k z}) := by
  intro τ hτ
  obtain ⟨c, hc, hb⟩ := ht τ hτ
  refine ⟨c, hc, ?_⟩
  filter_upwards [hb] with k hk
  rw [Data.sampleMeasure_apply p k (measurableSet_lt measurable_const
    (p.measurable_sampledDensity_of σ hg k))]
  exact hk

/-- The original weighted selected law is at most a probability law. -/
theorem Normalization.SampleProblem.weighted_mass_le_one
    {N K : ℝ} {M D W : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {P : Fin W → Test} {B : Fin W → ℝ}
    (hs : Normalization.SampleProblem N K M D W ω ν E P B) :
    (∑ b, ENNReal.ofReal (ω b) * (((ν b).prod volume).restrict (E b)) univ) ≤ 1 := by
  have hmass (b : Fin W) : (((ν b).prod volume).restrict (E b)) univ ≤ 1 := by
    letI : IsProbabilityMeasure (ν b) := hs.prob b
    rw [Measure.restrict_apply_univ]
    calc
      ((ν b).prod volume) (E b) ≤ ((ν b).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) :=
        measure_mono (hs.event_time b)
      _ = 1 := by simp
  calc
    _ ≤ ∑ b, ENNReal.ofReal (ω b) := Finset.sum_le_sum fun b _ => by
      simpa only [mul_one] using mul_le_mul' le_rfl (hmass b)
    _ = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => hs.weight_nonneg b), hs.weight_sum]
      norm_num

end Submission.Obl.k4_remainder_pure_profile_normalization
