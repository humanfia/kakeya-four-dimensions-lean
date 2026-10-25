import Submission.Obl.k4_native_calibrated_homogeneous_remainder.TypicalOperations
import Submission.Obl.k4_native_grid_profile_extension.CountedRefinement

/-! Subpower label coarsening preserves weighted typical exponents. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_native_grid_profile_extension
open Submission.Obl.k4_native_grid_profile_extension.Profiles
open Submission.Obl.k4_scalar_grid_density_extension

theorem typical_of_coarsening {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (Ω k)) (old current : (k : ℕ) → Ω k → ENNReal)
    (e : ℝ) (hold : HasTypicalDensity N μ old e)
    (hle : ∀ k, ∀ᵐ z ∂μ k, old k z ≤ current k z)
    (D : ℕ → ℝ)
    (hD : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, D k ≤ N k ^ ε)
    (htail : ∀ ε : ℝ, 0 < ε → ∀ k,
      μ k {z | old k z < ENNReal.ofReal (N k ^ (-ε)) * current k z} ≤
        ENNReal.ofReal (N k ^ (-ε) * D k)) : HasTypicalDensity N μ current e := by
  have hsmall := refinement_tail_isPowerSmall N hN μ current old 0 D
    (by simpa only [zero_add] using hD) (by simpa only [zero_add] using htail)
  have ht := typical_of_power_tails N hN hNt μ old current e 0 hold
  simp only [sub_zero] at ht
  apply ht
  · intro ε hε
    refine ⟨1, zero_lt_one, Eventually.of_forall fun k => ?_⟩
    have hscale : ENNReal.ofReal (N k ^ (0 - ε)) ≤ 1 := by
      simpa only [Real.rpow_zero, ENNReal.ofReal_one] using
        ofReal_rpow_le_ofReal_rpow (hN k) (show 0 - ε ≤ 0 by linarith)
    have hz : μ k {z | current k z < ENNReal.ofReal (N k ^ (0 - ε)) * old k z} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hle k] with z hz
      have hm := mul_le_mul' hscale (le_refl (old k z))
      rw [one_mul] at hm
      exact not_lt_of_ge (hm.trans hz)
    exact hz.le.trans zero_le
  · intro ε hε
    apply (hsmall ε hε).mono
    apply Eventually.of_forall
    intro k
    apply measure_mono
    intro z hz
    by_contra hn
    simp only [zero_add] at hn hz
    have hcmp := mul_le_mul' (le_refl (ENNReal.ofReal (N k ^ ε))) (not_lt.mp hn)
    rw [← mul_assoc, ofReal_rpow_mul_rpow (by linarith [hN k]), add_neg_cancel,
      Real.rpow_zero, ENNReal.ofReal_one, one_mul] at hcmp
    exact not_lt_of_ge hcmp hz

section
variable {Ω X B C : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace B] [Countable B] [MeasurableSingletonClass B]
  [MeasurableSpace C] [Countable C] [MeasurableSingletonClass C]

theorem weighted_refinement_density_le (ρ : Measure X) [SigmaFinite ρ]
    {W : ℕ} (ω : Fin W → ENNReal) (μ : Fin W → Measure Ω)
    (Q : Fin W → Ω → X × B) (hQ : ∀ b, Measurable (Q b)) (h : B → C)
    (f : Fin W → X × C → ENNReal) (g : Fin W → X × B → ENNReal)
    (hf : ∀ b, Measurable (f b)) (hg : ∀ b, Measurable (g b))
    (hfmap : ∀ b, (μ b).map (fun z => ((Q b z).1, h (Q b z).2)) =
      (ρ.prod Measure.count).withDensity (f b))
    (hgmap : ∀ b, (μ b).map (Q b) = (ρ.prod Measure.count).withDensity (g b)) :
    ∀ᵐ z ∂worldLaw ω μ, ω z.1 * g z.1 (Q z.1 z.2) ≤
      ω z.1 * f z.1 ((Q z.1 z.2).1, h (Q z.1 z.2).2) := by
  apply ae_worldLaw
  intro b
  filter_upwards [observation_refinement_density_le (μ b) ρ (Q b) (hQ b) h
    (f b) (g b) (hf b) (hg b) (hfmap b) (hgmap b)] with p hp
  exact mul_le_mul' le_rfl hp

theorem weighted_refinement_low_density_mass (ρ : Measure X)
    {W : ℕ} (ω : Fin W → ENNReal) (μ : Fin W → Measure Ω)
    (Q : Fin W → Ω → X × B) (hQ : ∀ b, Measurable (Q b)) (h : B → C)
    (ε D : ENNReal) (hD : ∀ c, Measure.count {b : B | h b = c} ≤ D)
    (f : Fin W → X × C → ENNReal) (g : Fin W → X × B → ENNReal)
    (hf : ∀ b, Measurable (f b)) (hg : ∀ b, Measurable (g b))
    (hfmap : ∀ b, (μ b).map (fun z => ((Q b z).1, h (Q b z).2)) =
      (ρ.prod Measure.count).withDensity (f b))
    (hgmap : ∀ b, (μ b).map (Q b) = (ρ.prod Measure.count).withDensity (g b)) :
    worldLaw ω μ {z | ω z.1 * g z.1 (Q z.1 z.2) <
      ε * (ω z.1 * f z.1 ((Q z.1 z.2).1, h (Q z.1 z.2).2))} ≤
        ε * D * worldLaw ω μ univ := by
  rw [worldLaw_apply, worldLaw_univ, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  have hsub : {z | ω b * g b (Q b z) < ε * (ω b * f b ((Q b z).1, h (Q b z).2))} ⊆
      {z | g b (Q b z) < ε * f b ((Q b z).1, h (Q b z).2)} := by
    intro z hz
    by_contra hn
    have hle := mul_le_mul' (le_refl (ω b)) (not_lt.mp hn)
    exact not_lt_of_ge (by simpa only [mul_left_comm] using hle) hz
  calc
    _ ≤ ω b * μ b {z | g b (Q b z) < ε * f b ((Q b z).1, h (Q b z).2)} :=
      mul_le_mul' le_rfl (measure_mono hsub)
    _ ≤ ω b * (ε * D * μ b univ) := mul_le_mul' le_rfl
      (observation_refinement_low_density_mass (μ b) ρ (Q b) (hQ b) h ε D hD
        (f b) (g b) (hf b) (hg b) (hfmap b) (hgmap b))
    _ = _ := by ring

end
end Submission.Obl.k4_native_calibrated_homogeneous_remainder
