import Submission.Obl.k4_native_calibrated_homogeneous_remainder.RawHomogenization
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.RawDensities
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.WeightedLabels
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-! The zero-angular-width slice gives a pure profile at the intrinsic phase. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_native_grid_profile_extension.Profiles

noncomputable def familyLaw (p : Data) (k : ℕ) : Measure (Fin (p.W k) × Incidence) :=
  worldLaw (fun b => ENNReal.ofReal (p.ω k b)) (selected p k)

theorem RawValid.family_mass_le_one {p : Data} (hp : RawValid p) (k : ℕ) :
    familyLaw p k univ ≤ 1 := by
  have hp0 := hp
  obtain ⟨-, -, -, -, -, -, -, -, M, D, hfmt⟩ := hp
  apply worldLaw_mass_le_one (fun b => ENNReal.ofReal (p.ω k b)) (selected p k)
  · rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => (hfmt k).2.1 b), (hfmt k).2.2.1]
    norm_num
  · exact fun b => hp0.selected_mass_le_one k b

theorem native_jobs_eq (B a u : ℝ) : Comp.jobs B a u =
    (fun z => (obs B a z, fun j : Fin 2 => ⌊v z.1 j / u⌋)) := rfl

/-- Canonical densities at the intrinsic phase have the weighted pure exponent
given by the joint profile's zero-width slice. -/
theorem WeightedJointTypical.intrinsic_pure {p : Data} (hp : RawValid p)
    {R U ρ₀ : ℝ} {F : ℝ → ℝ → ℝ} (ht : WeightedJointTypical p R U ρ₀ F)
    (hU : 0 ≤ U) (s : ℝ) (hs : 0 ≤ s) (hsR : s ≤ R) :
    HasTypicalDensity p.N (familyLaw p)
      (fun k z => ENNReal.ofReal (p.ω k z.1) *
        pureDensity hp k z.1 (Comp.theta (p.N k) ρ₀ s)
          (obs (p.B k z.1) (Comp.theta (p.N k) ρ₀ s) z.2)) (F (ρ₀ + s) 0) := by
  have hN : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.1 k]
  let α : ℕ → ℝ := fun k => Comp.theta (p.N k) ρ₀ s
  have hjoint : HasTypicalDensity p.N (familyLaw p)
      (fun k z => ENNReal.ofReal (p.ω k z.1) *
        jointDensity hp k z.1 (α k) 1
          (obs (p.B k z.1) (α k) z.2, fun j : Fin 2 => ⌊v z.2.1 j / (1 : ℝ)⌋))
        (F (ρ₀ + s) 0) := by
    intro τ hτ
    obtain ⟨c, hc, hev⟩ := ht s 0 τ hs hsR le_rfl hU hτ
    refine ⟨c, hc, ?_⟩
    filter_upwards [hev] with k hk
    rw [familyLaw, worldLaw_apply]
    have hz : Comp.dl (p.N k) 0 = 1 := by simp [Comp.dl]
    simp only [hz, native_jobs_eq] at hk
    exact hk (fun b => jointDensity hp k b (α k) 1)
      (fun b => jointDensity_spec hp k b (α k) 1)
  have hD : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, 49 * p.K k ^ 2 ≤ p.N k ^ ε := by
    intro ε hε
    have hh := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
      hN hp.2.1 hp.2.2.1.1 hp.2.2.1.2 2 hε (show (0 : ℝ) ≤ 49 by norm_num)
    simpa only [Real.rpow_zero, mul_one] using hh.mono (fun _ h => h.le)
  exact typical_of_finite_label_forgetting
    (volume.prod (Measure.count : Measure ℤ)) p.N hN hp.2.1 p.W
    (fun k b => ENNReal.ofReal (p.ω k b)) (selected p)
    (fun k b => obs (p.B k b) (α k))
    (fun _ _ z => fun j : Fin 2 => ⌊v z.1 j / (1 : ℝ)⌋)
    (fun k b => measurable_nativeObs _ _) (fun _ _ => measurable_velocityLabel 1)
    (fun k b => pureDensity hp k b (α k)) (fun k b => jointDensity hp k b (α k) 1)
    (fun k b => (pureDensity_spec hp k b (α k)).1)
    (fun k b => (jointDensity_spec hp k b (α k) 1).1)
    (fun k b => (pureDensity_spec hp k b (α k)).2)
    (fun k b => (jointDensity_spec hp k b (α k) 1).2)
    (fun k => Submission.Obl.k4_profile_density_bounds.velocityBins (p.K k))
    hp.unit_velocity_labels (fun k => 49 * p.K k ^ 2)
    (fun k => Submission.Obl.k4_profile_density_bounds.card_velocityBins_le (hp.2.2.1.1 k))
    hD hp.family_mass_le_one _ hjoint

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
