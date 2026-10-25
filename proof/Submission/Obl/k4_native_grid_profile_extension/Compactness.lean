/-
Adapted from this LOT tree, o075, session x0249, commit c9860862e62947c5fb8b3bc42c0a4ebc874a7eee,
Submission/Obl/k4_joint_homogenization/Compactness.lean. Earlier source attributions are retained below.
-/

import Submission.Obl.k4_native_grid_profile_extension.GridExtension
import Submission.Obl.k4_native_grid_profile_extension.Profiles.ExponentLimit

/-!
# Compactness of native joint density profiles
-/

namespace Submission.Obl.k4_native_grid_profile_extension

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Bounded grid exponents admit a subsequential regular profile, with typicality
at every depth and for every measurable density representative. -/
theorem native_grid_profile_extension
    (N K : ℕ → ℝ) (μ : ℕ → Measure (Coefficients × ℝ))
    (hN₂ : ∀ k, 2 ≤ N k) (hN : Tendsto N atTop atTop) (hK : Subpower N K)
    (hmass : ∀ k, μ k Set.univ ≤ 1)
    (hlower : ∀ k, ENNReal.ofReal ((K k)⁻¹) ≤ μ k Set.univ)
    (R U : ℝ) (hR : 0 < R) (hU : 0 < U)
    (hExists : DensityExists N μ R U) (hGrid : GridData N μ R U) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ F : ℝ → ℝ → ℝ,
      ProfileRegular R U F ∧
        Typical (fun k => N (ψ k)) (fun k => μ (ψ k)) R U F := by
  classical
  letI : ∀ k, IsFiniteMeasure (μ k) := fun k => ⟨lt_of_le_of_lt (hmass k) (by simp)⟩
  obtain ⟨A, a, ha, hgrid⟩ := hGrid
  let ar : ℕ → (ℚ × ℚ) → ℝ := fun k x => a k x.1 x.2
  have har (k : ℕ) (x : ℚ × ℚ) : ar k x ∈ Icc (-(A : ℝ)) (A : ℝ) :=
    abs_le.mp (ha k x.1 x.2)
  obtain ⟨ψ, g, hψ, hg, hlim⟩ := Profiles.countable_bounded_subsequence ar
    (fun _ => -(A : ℝ)) (fun _ => (A : ℝ)) har
  let Ns : ℕ → ℝ := N ∘ ψ
  let μs : ℕ → Measure (Coefficients × ℝ) := μ ∘ ψ
  letI : ∀ k, IsFiniteMeasure (μs k) := fun k => by
    simpa only [μs, Function.comp_apply] using
      (inferInstance : IsFiniteMeasure (μ (ψ k)))
  have hNs₂ (k : ℕ) : 2 ≤ Ns k := hN₂ (ψ k)
  have hNst : Tendsto Ns atTop atTop := hN.comp hψ.tendsto_atTop
  have hExistss : DensityExists Ns μs R U := fun k => hExists (ψ k)
  have hmasss (k : ℕ) : μs k Set.univ ≤ 1 := hmass (ψ k)
  have hnonzero : ¬ Profiles.IsPowerSmall Ns (fun k => μs k Set.univ) := by
    apply Profiles.not_isPowerSmall_of_inverse_subpower hNst
    intro ε hε
    filter_upwards [hψ.tendsto_atTop.eventually (hK.2 ε hε)] with k hk
    have hKpos : 0 < K (ψ k) := lt_of_lt_of_le zero_lt_one (hK.1 (ψ k))
    have hNpos : 0 < N (ψ k) := by linarith [hN₂ (ψ k)]
    have hinv : N (ψ k) ^ (-ε) ≤ (K (ψ k))⁻¹ := by
      rw [Real.rpow_neg hNpos.le]
      simpa only [one_div] using one_div_le_one_div_of_le hKpos hk
    exact (ENNReal.ofReal_le_ofReal hinv).trans (hlower (ψ k))
  have hgridfixed (q s : ℚ) :
      Profiles.HasTypicalDensity Ns μs
        (nativeDensityAt Ns μs (Clamp R q) (Clamp U s)) (g (q, s)) := by
    apply Profiles.hasTypicalDensity_of_exponent_tendsto Ns
      (fun k => by linarith [hNs₂ k]) μs
      (nativeDensityAt Ns μs (Clamp R q) (Clamp U s))
      (fun k => a (ψ k) q s) (g (q, s)) (hlim (q, s))
    intro τ hτ
    obtain ⟨c, hc, hbad⟩ := hgrid q s τ hτ
    refine ⟨c, hc, ?_⟩
    filter_upwards [hψ.tendsto_atTop.eventually hbad] with k hk
    have hr := clamp_mem hR.le q
    have hu := clamp_mem hU.le s
    have hcanon := nativeDensity_law (μ (ψ k)) (N (ψ k)) (Clamp R q) (Clamp U s)
      (hExists (ψ k) _ _ hr.1 hr.2 hu.1 hu.2)
    have hmap : (μ (ψ k)).map (Observation (N (ψ k)) (Clamp R q) (Clamp U s)) =
        Reference.withDensity (nativeDensity (μ (ψ k)) (N (ψ k)) (Clamp R q) (Clamp U s)) := by
      simpa only [nativeObservation_eq_Observation, nativeReference] using hcanon
    have hbound := hk _ (measurable_nativeDensity _ _ _ _) hmap
    simpa only [Ns, μs, Function.comp_apply, nativeDensityAt,
      nativeObservation_eq_Observation] using hbound
  let grid := depthGrid R ×ˢ depthGrid U
  let rep : grid → ℚ × ℚ := fun x =>
    (Classical.choose x.2.1, Classical.choose x.2.2)
  have hrep (x : grid) : Clamp R (rep x).1 = x.1.1 ∧ Clamp U (rep x).2 = x.1.2 :=
    ⟨Classical.choose_spec x.2.1, Classical.choose_spec x.2.2⟩
  have hgridprofile : ∀ x : grid,
      Profiles.HasTypicalDensity Ns μs (nativeDensityAt Ns μs x.1.1 x.1.2) (g (rep x)) := by
    intro x
    have h := hgridfixed (rep x).1 (rep x).2
    simpa only [(hrep x).1, (hrep x).2] using h
  obtain ⟨F, hF, htypical⟩ := extend_native_typical_grid Ns hNs₂ hNst μs hmasss
    hnonzero hR hU hExistss (fun x => g (rep x)) hgridprofile
  exact ⟨ψ, hψ, F, hF, typical_of_nativeDensity hExistss htypical⟩

end Submission.Obl.k4_native_grid_profile_extension
