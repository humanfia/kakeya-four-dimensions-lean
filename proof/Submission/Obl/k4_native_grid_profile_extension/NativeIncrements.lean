/-
Adapted from this LOT tree, o075, session x0249, commit c9860862e62947c5fb8b3bc42c0a4ebc874a7eee,
Submission/Obl/k4_joint_homogenization/NativeIncrements.lean. Earlier source attributions are retained below.
-/

import Submission.Obl.k4_native_grid_profile_extension.ProfileBridge

/-!
# Increment bounds for native limiting density exponents
-/

namespace Submission.Obl.k4_native_grid_profile_extension

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable def nativeDensityAt (N : ℕ → ℝ) (μ : ℕ → Measure (Coefficients × ℝ))
    (r u : ℝ) (k : ℕ) (p : Coefficients × ℝ) : ℝ≥0∞ :=
  nativeDensity (μ k) (N k) r u (nativeObservation (N k) r u p)

/-- The exact dyadic ambiguity count has the required asymptotic exponent. -/
theorem joint_refinement_count_subpower (N : ℕ → ℝ) (hN₂ : ∀ k, 2 ≤ N k)
    (hN : Tendsto N atTop atTop) {r s u v : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) (hu : 0 ≤ u) (huv : u ≤ v) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ((refinementDenominator (N k) r s * (refinementDenominator (N k) u v) ^ 2 : ℕ) : ℝ) ≤
        N k ^ (((s - r) + 2 * (v - u)) + ε) := by
  intro ε hε
  have hlarge : ∀ᶠ k in atTop, 8 ≤ N k ^ ε :=
    ((tendsto_rpow_atTop hε).comp hN).eventually (eventually_ge_atTop 8)
  filter_upwards [hlarge] with k hk
  have hNk : 1 ≤ N k := by linarith [hN₂ k]
  calc
    _ ≤ 8 * N k ^ ((s - r) + 2 * (v - u)) :=
      joint_refinement_count_le hNk hr hrs hu huv
    _ ≤ N k ^ ε * N k ^ ((s - r) + 2 * (v - u)) :=
      mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg (by linarith) _)
    _ = N k ^ (((s - r) + 2 * (v - u)) + ε) := by
      rw [← Real.rpow_add (by linarith : 0 < N k)]
      congr 1
      ring

/-- The native refinement low-tail estimate loses a power only according to
its one hidden and two angular coordinate increments. -/
theorem native_refinement_tail_isPowerSmall
    (N : ℕ → ℝ) (hN₂ : ∀ k, 2 ≤ N k) (hN : Tendsto N atTop atTop)
    (μ : ℕ → Measure (Coefficients × ℝ)) [∀ k, IsFiniteMeasure (μ k)]
    (hmass : ∀ k, μ k Set.univ ≤ 1)
    {R U : ℝ} (hExists : DensityExists N μ R U)
    {r s u v : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hsR : s ≤ R)
    (hu : 0 ≤ u) (huv : u ≤ v) (hvU : v ≤ U) :
    ∀ ε : ℝ, 0 < ε → Profiles.IsPowerSmall N (fun k =>
      μ k {p | nativeDensityAt N μ s v k p <
        ENNReal.ofReal (N k ^ (-(((s - r) + 2 * (v - u)) + ε))) *
          nativeDensityAt N μ r u k p}) := by
  let Δ := (s - r) + 2 * (v - u)
  let D : ℕ → ℝ := fun k =>
    ((refinementDenominator (N k) r s * (refinementDenominator (N k) u v) ^ 2 : ℕ) : ℝ)
  apply Profiles.refinement_tail_isPowerSmall N (fun k => by linarith [hN₂ k]) μ
    (nativeDensityAt N μ r u) (nativeDensityAt N μ s v) Δ D
    (joint_refinement_count_subpower N hN₂ hN hr hrs hu huv)
  intro ε hε k
  have hNk : 1 ≤ N k := by linarith [hN₂ k]
  have hcoarse := nativeDensity_law (μ k) (N k) r u
    (hExists k r u hr (hrs.trans hsR) hu (huv.trans hvU))
  have hfine := nativeDensity_law (μ k) (N k) s v
    (hExists k s v (hr.trans hrs) hsR (hu.trans huv) hvU)
  have ht := native_refinement_low_density_mass (μ k) hNk hr hrs hu huv
    (nativeDensity (μ k) (N k) r u) (nativeDensity (μ k) (N k) s v)
    (measurable_nativeDensity _ _ _ _) (measurable_nativeDensity _ _ _ _)
    hcoarse hfine (ENNReal.ofReal (N k ^ (-(Δ + ε))))
  refine ht.trans ?_
  calc
    _ ≤ ENNReal.ofReal (N k ^ (-(Δ + ε))) *
        ((refinementDenominator (N k) r s * (refinementDenominator (N k) u v) ^ 2 : ℕ) : ℝ≥0∞) *
          1 := mul_le_mul' le_rfl (hmass k)
    _ = ENNReal.ofReal (N k ^ (-(Δ + ε)) * D k) := by
      rw [mul_one, ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _)]
      simp only [D, ENNReal.ofReal_natCast]

/-- Typical exponents increase by at most the exact joint refinement exponent. -/
theorem native_density_exponent_increment
    (N : ℕ → ℝ) (hN₂ : ∀ k, 2 ≤ N k) (hN : Tendsto N atTop atTop)
    (μ : ℕ → Measure (Coefficients × ℝ)) [∀ k, IsFiniteMeasure (μ k)]
    (hmass : ∀ k, μ k Set.univ ≤ 1)
    (hnonzero : ¬ Profiles.IsPowerSmall N (fun k => μ k Set.univ))
    {R U : ℝ} (hExists : DensityExists N μ R U)
    {r s u v e₀ e₁ : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hsR : s ≤ R)
    (hu : 0 ≤ u) (huv : u ≤ v) (hvU : v ≤ U)
    (hcoarse : Profiles.HasTypicalDensity N μ (nativeDensityAt N μ r u) e₀)
    (hfine : Profiles.HasTypicalDensity N μ (nativeDensityAt N μ s v) e₁) :
    0 ≤ e₁ - e₀ ∧ e₁ - e₀ ≤ (s - r) + 2 * (v - u) := by
  apply Profiles.density_exponent_increment_of_refinement N hN₂ hN μ
    (nativeDensityAt N μ r u) (nativeDensityAt N μ s v) e₀ e₁
    ((s - r) + 2 * (v - u)) hnonzero hcoarse hfine
  · intro k
    exact native_refinement_density_le (μ k) (by linarith [hN₂ k]) hr hrs hu huv
      _ _ (measurable_nativeDensity _ _ _ _) (measurable_nativeDensity _ _ _ _)
      (nativeDensity_law (μ k) (N k) r u
        (hExists k r u hr (hrs.trans hsR) hu (huv.trans hvU)))
      (nativeDensity_law (μ k) (N k) s v
        (hExists k s v (hr.trans hrs) hsR (hu.trans huv) hvU))
  · exact native_refinement_tail_isPowerSmall N hN₂ hN μ hmass hExists hr hrs hsR hu huv hvU

end Submission.Obl.k4_native_grid_profile_extension
