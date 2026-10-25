import Submission.Obl.k4_horizon_light_cell_mass.World
import Submission.Obl.k4_native_grid_profile_extension.Profiles.TypicalDensity

namespace Submission.Obl.k4_horizon_light_cell_mass

open MeasureTheory Set Filter
open scoped ENNReal Topology
open Submission.Obl.k4_native_base_flattening (NativeMixtureFormat exists_uniform_mesh_exponent)
open Submission.Obl.k4_native_grid_profile_extension.Profiles (IsPowerSmall)

/-- Quantitative rectangular flattening and density typicality imply the uniform light-cell tail. -/
theorem weighted_light_cells
    (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (M D : ℕ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (hω : ∀ k γ, 0 ≤ ω k γ) (hωsum : ∀ k, ∑ γ, ω k γ = 1)
    (μ : (k : ℕ) → Fin (W k) → Measure State)
    (B : (k : ℕ) → Fin (W k) → ℝ) (a : ℕ → ℝ)
    (g : (k : ℕ) → Fin (W k) → Observation → ℝ≥0∞) (b : ℝ)
    (hsource : ∀ k γ, ∃ f : Raw → ℝ, NativeMixtureFormat (N k) M D f ∧ Measurable f ∧
      (∀ x, 0 ≤ f x) ∧ (∀ x, |f x| ≤ N k ^ (2 * M)) ∧
      (μ k γ).map rawChart = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hg : ∀ k γ, Measurable (g k γ) ∧
      (μ k γ).map (pureMap (B k γ) (a k)) = reference.withDensity (g k γ))
    (htyp : ∀ τ : ℝ, 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      (∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ)
        {p | g k γ (pureMap (B k γ) (a k) p) < ENNReal.ofReal (N k ^ (-b - τ))}) ≤
          ENNReal.ofReal (N k ^ (-c))) :
    ∃ H₀ : ℝ, ∀ τ : ℝ, 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∀ ρ₁ ρ₂ : ℝ, 0 < ρ₁ → ρ₁ ≤ N k ^ (-H₀) → 0 < ρ₂ → ρ₂ ≤ N k ^ (-H₀) →
        (∑ γ, ENNReal.ofReal (ω k γ) *
          lightMass (μ k γ) (B k γ) (a k) ρ₁ ρ₂ (N k ^ (-b - τ))) ≤
            ENNReal.ofReal (N k ^ (-c)) := by
  obtain ⟨H, hH⟩ := exists_uniform_mesh_exponent M (1769472 * (D : ℝ)) 1
  refine ⟨(H : ℝ), ?_⟩
  intro τ hτ
  have hτ2 : 0 < τ / 2 := by positivity
  let bad : ℕ → ℝ≥0∞ := fun k => ∑ γ, ENNReal.ofReal (ω k γ) * (μ k γ)
    {p | g k γ (pureMap (B k γ) (a k) p) < ENNReal.ofReal (N k ^ (-b - τ / 2))}
  have hb : IsPowerSmall N bad := htyp (τ / 2) hτ2
  have he : IsPowerSmall N (fun k => ENNReal.ofReal (N k ^ (-1 : ℝ))) :=
    ⟨1, by norm_num, Eventually.of_forall (fun _ => le_rfl)⟩
  obtain ⟨c, hc, hbound⟩ := he.add hNt hb
  have hfour : ∀ᶠ k in atTop, 4 ≤ N k ^ (τ / 2) :=
    ((tendsto_rpow_atTop hτ2).comp hNt).eventually (eventually_ge_atTop 4)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hbound, hfour] with k hk hfour
  intro ρ₁ ρ₂ hρ₁ hρ₁H hρ₂ hρ₂H
  have hNk : 0 < N k := by linarith [hN k]
  have hmesh : N k ^ (-(H : ℝ)) = (N k ^ H)⁻¹ := by
    rw [Real.rpow_neg hNk.le, Real.rpow_natCast]
  have hmax : max ρ₁ ρ₂ ≤ (N k ^ H)⁻¹ := by rw [← hmesh]; exact max_le hρ₁H hρ₂H
  have herr : 1769472 * (D : ℝ) * (N k ^ M) ^ 9 * max ρ₁ ρ₂ ≤ N k ^ (-1 : ℝ) := by
    calc
      _ ≤ 1769472 * (D : ℝ) * (N k ^ M) ^ 9 * (N k ^ H)⁻¹ :=
        mul_le_mul_of_nonneg_left hmax (by positivity)
      _ ≤ (N k ^ (1 : ℕ))⁻¹ := (hH (N k) (hN k)).1
      _ = _ := by rw [pow_one, Real.rpow_neg_one]
  have hthreshold : 4 * ENNReal.ofReal (N k ^ (-b - τ)) ≤
      ENNReal.ofReal (N k ^ (-b - τ / 2)) := by
    calc
      _ = ENNReal.ofReal (4 * N k ^ (-b - τ)) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        calc
          _ ≤ N k ^ (τ / 2) * N k ^ (-b - τ) :=
            mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg hNk.le _)
          _ = N k ^ (-b - τ / 2) := by rw [← Real.rpow_add hNk]; congr 1; ring)
  have hworld (γ : Fin (W k)) :
      lightMass (μ k γ) (B k γ) (a k) ρ₁ ρ₂ (N k ^ (-b - τ)) ≤
        ENNReal.ofReal (N k ^ (-1 : ℝ)) + (μ k γ)
          {p | g k γ (pureMap (B k γ) (a k) p) < ENNReal.ofReal (N k ^ (-b - τ / 2))} := by
    obtain ⟨f, hf, hfm, hf0, hfb, hraw⟩ := hsource k γ
    refine (formatted_lightMass_le (N k) M D (hN k) (μ k γ) (B k γ) (a k)
      f hf hfm hf0 hfb hraw (g k γ) (hg k γ).1 (hg k γ).2
      ρ₁ ρ₂ (N k ^ (-b - τ)) hρ₁ hρ₂ (Real.rpow_nonneg hNk.le _)).trans ?_
    apply add_le_add (ENNReal.ofReal_le_ofReal herr)
    exact measure_mono (fun p hp => hp.trans_le hthreshold)
  have hsum : ∑ γ, ENNReal.ofReal (ω k γ) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun γ _ => hω k γ), hωsum]
    norm_num
  calc
    _ ≤ ∑ γ, ENNReal.ofReal (ω k γ) *
        (ENNReal.ofReal (N k ^ (-1 : ℝ)) + (μ k γ)
          {p | g k γ (pureMap (B k γ) (a k) p) < ENNReal.ofReal (N k ^ (-b - τ / 2))}) := by
      apply Finset.sum_le_sum
      intro γ _
      gcongr
      exact hworld γ
    _ = ENNReal.ofReal (N k ^ (-1 : ℝ)) + bad k := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul]
    _ ≤ _ := hk

end Submission.Obl.k4_horizon_light_cell_mass
