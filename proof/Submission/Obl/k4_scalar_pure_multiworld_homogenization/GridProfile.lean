import Submission.Lib.K4Homogenization.ProfileCompactness
import Submission.Obl.k4_native_grid_profile_extension.Profiles.ProfileCompactness
import Submission.Obl.k4_native_grid_profile_extension.Profiles.ExponentLimit
import Submission.Obl.k4_scalar_grid_density_extension.GridTypical

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set Filter
open scoped ENNReal Topology
open Submission.Obl.k4_native_grid_profile_extension.Profiles

/-- The profile argument allows varying spaces, so a state may include its world.
The sampled densities remain the densities within that world. -/
theorem profile_of_countable_grid
    {α : ℕ → Type*} [∀ k, MeasurableSpace (α k)]
    (N : ℕ → ℝ) (hN₂ : ∀ k, 2 ≤ N k) (hN : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (α k))
    (hmass : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ENNReal.ofReal (N k ^ (-ε)) ≤ μ k univ)
    (L : ℝ) (hL : 0 ≤ L) (S : Set ℝ) (hS : S.Countable)
    (hclosure : closure S = Icc 0 L) (hzero : 0 ∈ S) (hend : L ∈ S)
    (g : ℝ → (k : ℕ) → α k → ENNReal)
    (a : ℕ → S → ℝ) (M : ℝ) (ha : ∀ k s, |a k s| ≤ M)
    (htypical : ∀ s : S, ∀ τ : ℝ, 0 < τ →
      IsPowerSmall N (fun k => μ k
        {z | g s k z < ENNReal.ofReal (N k ^ (-a k s - τ)) ∨
          ENNReal.ofReal (N k ^ (-a k s + τ)) < g s k z}))
    (hmono : ∀ r ∈ Icc 0 L, ∀ s ∈ Icc 0 L, r ≤ s →
      ∀ ε : ℝ, 0 < ε → IsPowerSmall N (fun k => μ k
        {z | g r k z < ENNReal.ofReal (N k ^ (-ε)) * g s k z}))
    (htail : ∀ r ∈ Icc 0 L, ∀ s ∈ Icc 0 L, r ≤ s →
      ∀ ε : ℝ, 0 < ε → IsPowerSmall N (fun k => μ k
        {z | g s k z < ENNReal.ofReal (N k ^ (-(s - r + ε))) * g r k z})) :
    ∃ (φ : ℕ → ℕ) (F : ℝ → ℝ), StrictMono φ ∧ LipschitzWith 1 F ∧
      (∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ L →
        0 ≤ F s - F r ∧ F s - F r ≤ s - r) ∧
      ∀ r ∈ Icc 0 L, HasTypicalDensity (N ∘ φ)
        (fun k => μ (φ k)) (fun k => g r (φ k)) (F r) := by
  classical
  let : Countable S := hS
  obtain ⟨b, φ, hφ, hlim, hb⟩ :=
    Submission.Lib.K4Homogenization.bounded_profile_subsequence a M ha
  let Ns : ℕ → ℝ := N ∘ φ
  let μs : (k : ℕ) → Measure (α (φ k)) := fun k => μ (φ k)
  have hNs₂ (k : ℕ) : 2 ≤ Ns k := hN₂ (φ k)
  have hNs₁ (k : ℕ) : 1 ≤ Ns k := by linarith [hNs₂ k]
  have hNst : Tendsto Ns atTop atTop := hN.comp hφ.tendsto_atTop
  have hmasss : ¬ IsPowerSmall Ns (fun k => μs k univ) :=
    not_isPowerSmall_of_inverse_subpower hNst
      (fun ε hε => hφ.tendsto_atTop.eventually (hmass ε hε))
  have hgrid (s : S) : HasTypicalDensity Ns μs (fun k => g s (φ k)) (b s) := by
    apply hasTypicalDensity_of_exponent_tendsto Ns hNs₁ μs
      (fun k => g s (φ k)) (fun k => a (φ k) s) (b s) (hlim s)
    intro τ hτ
    exact (htypical s τ hτ).comp φ hφ.tendsto_atTop
  have hmem (s : S) : (s : ℝ) ∈ Icc 0 L :=
    hclosure ▸ subset_closure s.property
  have hinc (r s : S) (hrs : (r : ℝ) ≤ s) :
      0 ≤ b s - b r ∧ b s - b r ≤ (s : ℝ) - r := by
    apply Submission.Obl.k4_scalar_grid_density_extension.density_exponent_increment_approx
      Ns hNs₂ hNst μs (fun k => g r (φ k)) (fun k => g s (φ k))
      (b r) (b s) ((s : ℝ) - r) hmasss (hgrid r) (hgrid s)
    · intro ε hε
      exact (hmono r (hmem r) s (hmem s) hrs ε hε).comp φ hφ.tendsto_atTop
    · intro ε hε
      exact (htail r (hmem r) s (hmem s) hrs ε hε).comp φ hφ.tendsto_atTop
  obtain ⟨F, hF, hFb, hshape⟩ := extend_profile_from_grid b hinc
  refine ⟨φ, F, hφ, hF, ?_, ?_⟩
  · intro r s hr hrs hs
    exact hshape r (hclosure.symm ▸ ⟨hr, hrs.trans hs⟩)
      s (hclosure.symm ▸ ⟨hr.trans hrs, hs⟩) hrs
  · apply Submission.Obl.k4_scalar_grid_density_extension.hasTypicalDensity_on_Icc_of_grid_approx
      Ns hNs₁ hNst μs (fun r k => g r (φ k)) F hF.continuous
      hL S hclosure hzero hend
    · intro r hr
      simpa only [hFb ⟨r, hr⟩] using hgrid ⟨r, hr⟩
    · intro r hr s hs hrs ε hε
      exact (hmono r hr s hs hrs ε hε).comp φ hφ.tendsto_atTop

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
