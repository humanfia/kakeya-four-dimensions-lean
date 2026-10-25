import Submission.Obl.k4_native_calibrated_homogeneous_remainder.FiniteLabels
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.TypicalOperations

/-! Forgetting a subpower finite label in a weighted family of worlds. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_native_grid_profile_extension.Profiles
open Submission.Obl.k4_scalar_grid_density_extension

section
variable {X I Ω : Type*} [MeasurableSpace X] [MeasurableSpace I] [MeasurableSpace Ω]
  [Countable I] [MeasurableSingletonClass I]

/-- The finite-label low-tail estimate keeps the original world weights. -/
theorem weighted_finite_label_lowDensity_mass (ρ : Measure X) [SigmaFinite ρ]
    {W : ℕ} (ω : Fin W → ENNReal) (μ : Fin W → Measure Ω)
    (obs : Fin W → Ω → X) (label : Fin W → Ω → I)
    (hobs : ∀ b, Measurable (obs b)) (hlabel : ∀ b, Measurable (label b))
    (g : Fin W → X → ENNReal) (G : Fin W → X × I → ENNReal)
    (hg : ∀ b, Measurable (g b)) (hG : ∀ b, Measurable (G b))
    (hpure : ∀ b, (μ b).map (obs b) = ρ.withDensity (g b))
    (hjoint : ∀ b, (μ b).map (fun p => (obs b p, label b p)) =
      (ρ.prod Measure.count).withDensity (G b))
    (L : Finset I) (hL : ∀ b, ∀ᵐ p ∂μ b, label b p ∈ L) (ε : ENNReal) :
    worldLaw ω μ {z | ω z.1 * G z.1 (obs z.1 z.2, label z.1 z.2) <
      ε * (ω z.1 * g z.1 (obs z.1 z.2))} ≤
      ε * (L.card : ENNReal) * worldLaw ω μ univ := by
  rw [worldLaw_apply, worldLaw_univ, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  have hsub : {p | ω b * G b (obs b p, label b p) < ε * (ω b * g b (obs b p))} ⊆
      {p | G b (obs b p, label b p) < ε * g b (obs b p)} := by
    intro p hp
    by_contra hn
    have hle := mul_le_mul' (le_refl (ω b)) (not_lt.mp hn)
    exact not_lt_of_ge (by simpa only [mul_left_comm] using hle) hp
  calc
    _ ≤ ω b * μ b {p | G b (obs b p, label b p) < ε * g b (obs b p)} :=
      mul_le_mul' le_rfl (measure_mono hsub)
    _ ≤ ω b * (ε * (L.card : ENNReal) * μ b univ) := mul_le_mul' le_rfl
      (finite_label_lowDensity_mass ρ (μ b) (obs b) (label b) (hobs b) (hlabel b)
        (g b) (G b) (hg b) (hG b) (hpure b) (hjoint b) L (hL b) ε)
    _ = _ := by ring

/-- A weighted joint profile becomes a weighted marginal profile when the
discarded labels have subpower cardinality. -/
theorem typical_of_finite_label_forgetting (ρ : Measure X) [SigmaFinite ρ]
    (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ENNReal)
    (μ : (k : ℕ) → Fin (W k) → Measure Ω)
    (obs : (k : ℕ) → Fin (W k) → Ω → X)
    (label : (k : ℕ) → Fin (W k) → Ω → I)
    (hobs : ∀ k b, Measurable (obs k b)) (hlabel : ∀ k b, Measurable (label k b))
    (g : (k : ℕ) → Fin (W k) → X → ENNReal)
    (G : (k : ℕ) → Fin (W k) → X × I → ENNReal)
    (hg : ∀ k b, Measurable (g k b)) (hG : ∀ k b, Measurable (G k b))
    (hpure : ∀ k b, (μ k b).map (obs k b) = ρ.withDensity (g k b))
    (hjoint : ∀ k b, (μ k b).map (fun p => (obs k b p, label k b p)) =
      (ρ.prod Measure.count).withDensity (G k b))
    (L : ℕ → Finset I) (hL : ∀ k b, ∀ᵐ p ∂μ k b, label k b p ∈ L k)
    (D : ℕ → ℝ) (hcard : ∀ k, ((L k).card : ℝ) ≤ D k)
    (hD : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, D k ≤ N k ^ ε)
    (hmass : ∀ k, worldLaw (ω k) (μ k) univ ≤ 1) (e : ℝ)
    (hold : HasTypicalDensity N (fun k => worldLaw (ω k) (μ k))
      (fun k z => ω k z.1 * G k z.1 (obs k z.1 z.2, label k z.1 z.2)) e) :
    HasTypicalDensity N (fun k => worldLaw (ω k) (μ k))
      (fun k z => ω k z.1 * g k z.1 (obs k z.1 z.2)) e := by
  have hle : ∀ k, ∀ᵐ z ∂worldLaw (ω k) (μ k),
      ω k z.1 * G k z.1 (obs k z.1 z.2, label k z.1 z.2) ≤
        ω k z.1 * g k z.1 (obs k z.1 z.2) := by
    intro k
    apply ae_worldLaw
    intro b
    filter_upwards [counted_density_le_marginal ρ (μ k b) (obs k b) (label k b)
      (hobs k b) (hlabel k b) (g k b) (G k b) (hg k b) (hG k b)
      (hpure k b) (hjoint k b)] with p hp
    exact mul_le_mul' le_rfl hp
  have htail : ∀ ε : ℝ, 0 < ε → ∀ k,
      worldLaw (ω k) (μ k) {z | ω k z.1 * G k z.1 (obs k z.1 z.2, label k z.1 z.2) <
        ENNReal.ofReal (N k ^ (-ε)) * (ω k z.1 * g k z.1 (obs k z.1 z.2))} ≤
        ENNReal.ofReal (N k ^ (-ε) * D k) := by
    intro ε hε k
    have hcard' : ((L k).card : ENNReal) ≤ ENNReal.ofReal (D k) := by
      exact_mod_cast ENNReal.ofReal_le_ofReal (hcard k)
    calc
      _ ≤ ENNReal.ofReal (N k ^ (-ε)) * ((L k).card : ENNReal) *
          worldLaw (ω k) (μ k) univ :=
        weighted_finite_label_lowDensity_mass ρ (ω k) (μ k) (obs k) (label k)
          (hobs k) (hlabel k) (g k) (G k) (hg k) (hG k) (hpure k) (hjoint k)
          (L k) (hL k) _
      _ ≤ ENNReal.ofReal (N k ^ (-ε)) * ENNReal.ofReal (D k) * 1 :=
        mul_le_mul' (mul_le_mul' le_rfl hcard') (hmass k)
      _ = _ := by rw [mul_one, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith [hN k]) _)]
  have hsmall := refinement_tail_isPowerSmall N hN
    (fun k => worldLaw (ω k) (μ k))
    (fun k z => ω k z.1 * g k z.1 (obs k z.1 z.2))
    (fun k z => ω k z.1 * G k z.1 (obs k z.1 z.2, label k z.1 z.2)) 0 D
    (by simpa only [zero_add] using hD) (by simpa only [zero_add] using htail)
  have ht := typical_of_power_tails N hN hNt (fun k => worldLaw (ω k) (μ k))
    (fun k z => ω k z.1 * G k z.1 (obs k z.1 z.2, label k z.1 z.2))
    (fun k z => ω k z.1 * g k z.1 (obs k z.1 z.2)) e 0 hold
  simp only [sub_zero] at ht
  apply ht
  · intro ε hε
    refine ⟨1, zero_lt_one, Eventually.of_forall fun k => ?_⟩
    have hscale : ENNReal.ofReal (N k ^ (0 - ε)) ≤ 1 := by
      simpa only [Real.rpow_zero, ENNReal.ofReal_one] using
        ofReal_rpow_le_ofReal_rpow (hN k) (show 0 - ε ≤ 0 by linarith)
    have hz : worldLaw (ω k) (μ k) {z |
        ω k z.1 * g k z.1 (obs k z.1 z.2) < ENNReal.ofReal (N k ^ (0 - ε)) *
          (ω k z.1 * G k z.1 (obs k z.1 z.2, label k z.1 z.2))} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hle k] with z hz
      have hm := mul_le_mul' hscale (le_refl (ω k z.1 * G k z.1
        (obs k z.1 z.2, label k z.1 z.2)))
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

end
end Submission.Obl.k4_native_calibrated_homogeneous_remainder
