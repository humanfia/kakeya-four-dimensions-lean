import Submission.Obl.k4_oss_flat_decay.Sampling
import Submission.Obl.k4_oss_flat_decay.FlatnessNumerics
import LeanPool.NavierStokesAndEuler.Euler.LpParameterIntegral

namespace Submission.Obl.k4_oss_flat_decay

open MeasureTheory Set
open scoped MeasureTheory ENNReal NNReal

theorem integral_exp_product_eq_charFun (α β : Measure ℝ)
    [IsProbabilityMeasure α] [IsProbabilityMeasure β] (q : ℝ) :
    (∫ p : ℝ × ℝ, Complex.exp (((q * p.1 * p.2 : ℝ) : ℂ) * Complex.I) ∂(α.prod β)) =
      ∫ y, charFun α (q * y) ∂β := by
  have hi : Integrable (fun p : ℝ × ℝ =>
      Complex.exp (((q * p.1 * p.2 : ℝ) : ℂ) * Complex.I)) (α.prod β) :=
    (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun p => by
      simp only [Complex.norm_exp_ofReal_mul_I, le_refl])
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [charFun_apply_real]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  push_cast
  ring

/-- An almost-flat collision bound and a Frostman sampling law give bilinear
Fourier decay. The physical frequency window is enlarged by a fixed factor. -/
theorem flatness_decay_charFun {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ γ ε τ r₀ : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < ε ∧ 0 < τ ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r < r₀ →
      ∀ α β : Measure ℝ, IsProbabilityMeasure α → IsProbabilityMeasure β →
      α (Icc (-1 : ℝ) 1)ᶜ = 0 → β (Icc (-2 : ℝ) 2)ᶜ = 0 →
      collisionMass α r ≤ ENNReal.ofReal (r ^ (1 - γ)) →
      (∀ x u : ℝ, r ≤ u → u ≤ 1 →
        β (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-ε) * u ^ s)) →
      ∀ q : ℝ, r⁻¹ ≤ |q| → |q| ≤ 100 * r⁻¹ →
      ‖∫ y, charFun α (q * y) ∂β‖ ≤ r ^ τ := by
  let a : ℝ := s / 8
  have ha : 0 < a := by dsimp [a]; linarith
  let D : ℝ := 20000 * Real.pi + 200
  obtain ⟨r₀, hr₀, hr₀1, hD⟩ := exists_scale_absorb_constant D (a / 2) (by linarith)
  refine ⟨a, a, a / 4, r₀, ha, by dsimp [a]; linarith,
    ha, by positivity, hr₀, ?_⟩
  intro r hr hrr α β hαprob hβprob hαsupp hβsupp hflat hcap q hqlo hqhi
  let : IsProbabilityMeasure α := hαprob
  let : IsProbabilityMeasure β := hβprob
  have hr1 : r ≤ 1 := hrr.le.trans hr₀1
  have hq : q ≠ 0 := abs_pos.mp ((inv_pos.mpr hr).trans_le hqlo)
  have hη : 0 < r ^ (1 + a) := Real.rpow_pos_of_pos hr _
  have hηr : r ^ (1 + a) ≤ r := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hr hr1 (show (1 : ℝ) ≤ 1 + a by linarith)
  have hρ : 0 < r / 10000 := by positivity
  have hflatρ : collisionMass α (2 * (r / 10000)) ≤ ENNReal.ofReal (r ^ (1 - a)) :=
    (collisionMass_mono α (by linarith : 2 * (r / 10000) ≤ r)).trans hflat
  have hraw := charFun_sampling_sq_le_collision α β hαsupp hβsupp
    (η := r ^ (1 + a)) (r := r) (ρ := r / 10000) (q := q)
    (C := r ^ (-a)) (s := s) (A := r ^ (1 - a))
    hη hηr hr1 hρ hq (flatness_scale_budget hr hqhi)
    (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hr.le _)
    (fun x => hcap x r le_rfl hr1) hflatρ
  have hInv : |q⁻¹| ≤ r := by
    rw [abs_inv]
    have h := (inv_le_inv₀ (abs_pos.mpr hq) (inv_pos.mpr hr)).mpr hqlo
    simpa only [inv_inv] using h
  have hmain : (r ^ (-a) * r ^ s / (2 * r ^ (1 + a))) * |q⁻¹| *
        (4 * Real.pi / (r / 10000)) * r ^ (1 - a) ≤
      (20000 * Real.pi) * r ^ a := by
    calc
      _ ≤ (r ^ (-a) * r ^ s / (2 * r ^ (1 + a))) * r *
          (4 * Real.pi / (r / 10000)) * r ^ (1 - a) := by gcongr
      _ = (20000 * Real.pi) * r ^ (s - 3 * a) := flatness_coefficient_identity hr a s
      _ ≤ (20000 * Real.pi) * r ^ a := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by dsimp [a]; linarith)) (by positivity)
  have hnoise : 2 * |q| * r ^ (1 + a) ≤ 200 * r ^ a := by
    calc _ ≤ 2 * (100 * r⁻¹) * r ^ (1 + a) := by gcongr
      _ = _ := flatness_noise_identity hr a
  have havg : (∫ y, ‖charFun α (q * y)‖ ^ 2 ∂β) ≤ D * r ^ a := by
    dsimp [D]
    nlinarith [hraw, hmain, hnoise]
  have hmem : MemLp (fun y => charFun α (q * y)) 2 β :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr (integrable_charFun_sq_comp α β q)
  have hcs : ‖∫ y, charFun α (q * y) ∂β‖ ^ 2 ≤
      ∫ y, ‖charFun α (q * y)‖ ^ 2 ∂β := by
    simpa using EulerLpParameterIntegral.norm_integral_sq_le β _ hmem
  apply (sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg hr.le _)).mp
  calc
    _ ≤ D * r ^ a := hcs.trans havg
    _ ≤ r ^ (-(a / 2)) * r ^ a :=
      mul_le_mul_of_nonneg_right (hD r hr hrr) (Real.rpow_nonneg hr.le _)
    _ = (r ^ (a / 4)) ^ 2 := by
      rw [← Real.rpow_add hr, ← Real.rpow_mul_natCast hr.le]
      congr 1 <;> norm_num <;> ring

/-- Flatness-to-Fourier decay in the product-integral convention of o004.
The statement uses only Mathlib objects. -/
theorem fourier_decay_of_collision_flatness :
    ∀ s : ℝ, 0 < s → s ≤ 1 →
      ∃ γ ε τ r₀ : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < ε ∧ 0 < τ ∧ 0 < r₀ ∧
        ∀ r : ℝ, 0 < r → r < r₀ →
        ∀ α β : Measure ℝ, IsProbabilityMeasure α → IsProbabilityMeasure β →
        α (Icc (-1 : ℝ) 1)ᶜ = 0 → β (Icc (1 : ℝ) 2)ᶜ = 0 →
        (α.prod α) {p : ℝ × ℝ | |p.1 - p.2| ≤ r} ≤ ENNReal.ofReal (r ^ (1 - γ)) →
        (∀ x u : ℝ, r ≤ u → u ≤ 1 →
          β (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-ε) * u ^ s)) →
        ∀ ξ : ℝ, r⁻¹ ≤ |ξ| → |ξ| ≤ 2 * r⁻¹ →
        ‖∫ p : ℝ × ℝ,
          Complex.exp (((-2 * Real.pi * ξ * p.1 * p.2 : ℝ) : ℂ) * Complex.I)
          ∂(α.prod β)‖ ≤ r ^ τ := by
  intro s hs hs1
  obtain ⟨γ, ε, τ, r₀, hγ, hγ1, hε, hτ, hr₀, hdecay⟩ := flatness_decay_charFun hs hs1
  refine ⟨γ, ε, τ, r₀, hγ, hγ1, hε, hτ, hr₀, ?_⟩
  intro r hr hrr α β hαprob hβprob hαsupp hβsupp hflat hcap ξ hξlo hξhi
  let : IsProbabilityMeasure α := hαprob
  let : IsProbabilityMeasure β := hβprob
  have hβ2 : β (Icc (-2 : ℝ) 2)ᶜ = 0 := by
    have hsub : Icc (1 : ℝ) 2 ⊆ Icc (-2 : ℝ) 2 := Icc_subset_Icc (by norm_num) le_rfl
    exact le_antisymm ((measure_mono (compl_subset_compl.mpr hsub)).trans_eq hβsupp) bot_le
  have hqabs : |(-2 * Real.pi * ξ : ℝ)| = (2 * Real.pi) * |ξ| := by
    norm_num [abs_mul, abs_of_pos Real.pi_pos]
  have hqlo : r⁻¹ ≤ |(-2 * Real.pi * ξ : ℝ)| := by
    rw [hqabs]
    calc r⁻¹ = 1 * r⁻¹ := by ring
      _ ≤ (2 * Real.pi) * r⁻¹ := mul_le_mul_of_nonneg_right
        (by nlinarith [Real.pi_gt_three] : (1 : ℝ) ≤ 2 * Real.pi) (inv_nonneg.mpr hr.le)
      _ ≤ (2 * Real.pi) * |ξ| := mul_le_mul_of_nonneg_left hξlo (by positivity)
  have hqhi : |(-2 * Real.pi * ξ : ℝ)| ≤ 100 * r⁻¹ := by
    rw [hqabs]
    calc (2 * Real.pi) * |ξ| ≤ (2 * Real.pi) * (2 * r⁻¹) := by gcongr
      _ = (4 * Real.pi) * r⁻¹ := by ring
      _ ≤ 100 * r⁻¹ := mul_le_mul_of_nonneg_right
        (by nlinarith [Real.pi_lt_four] : (4 : ℝ) * Real.pi ≤ 100) (inv_nonneg.mpr hr.le)
  rw [integral_exp_product_eq_charFun]
  exact hdecay r hr hrr α β hαprob hβprob hαsupp hβ2 hflat hcap
    (-2 * Real.pi * ξ) hqlo hqhi

end Submission.Obl.k4_oss_flat_decay
