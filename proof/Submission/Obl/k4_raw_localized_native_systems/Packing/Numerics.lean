/- Adapted from this LOT tree, o197, session x0690, Packing/Numerics.lean,
   branch snapshot 9f1b6476; preserving original attributions below. -/
import Submission.Obl.k4_raw_localized_native_systems.Definitions
import Submission.Obl.k4_matching_abstract_switching_mixture.Scales

namespace Submission.Obl.k4_raw_localized_native_systems.Packing

noncomputable section

/-- Polynomial slack and the density-profile difference are the only costs
after the common physical tube volume and the witness saturation floor cancel. -/
theorem packing_power_ratio {N K C A a b ζ H : ℝ} (P : ℕ)
    (hN : 1 ≤ N) (hK : 0 < K) (hA : 0 ≤ A)
    (hpoly : C * K ^ (P + 1) ≤ N ^ ζ) (hexp : a + ζ ≤ b + H) :
    C * K ^ P * N ^ a * A ≤ (N ^ b * A / K) * N ^ H := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hscaled : (C * K ^ P * N ^ a * A) * K ≤ (N ^ b * A) * N ^ H := by
    calc
      _ = (C * K ^ (P + 1)) * N ^ a * A := by rw [pow_succ]; ring
      _ ≤ N ^ ζ * N ^ a * A :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hN0.le _)) hA
      _ = N ^ (a + ζ) * A := by rw [Real.rpow_add hN0]; ring
      _ ≤ N ^ (b + H) * A :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN hexp) hA
      _ = _ := by rw [Real.rpow_add hN0]; ring
  rw [show (N ^ b * A / K) * N ^ H = (N ^ b * A * N ^ H) / K by ring]
  exact (le_div_iff₀ hK).mpr hscaled

theorem exists_packing_polynomial_allowance (C : ℝ) (hC : 0 ≤ C) (P : ℕ)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ ε N₀ : ℝ, 0 < ε ∧ 2 ≤ N₀ ∧ ∀ N K : ℝ,
      N₀ ≤ N → 1 ≤ K → K ≤ N ^ ε → C * K ^ (P + 1) ≤ N ^ ζ := by
  obtain ⟨ε, hε, N₀, hN₀, h⟩ :=
    k4_matching_abstract_switching_mixture.absorb_polynomial C hC (P + 1) (by omega) ζ hζ
  refine ⟨ε, N₀, hε, hN₀, ?_⟩
  intro N K hN hK hKbound
  have hN1 : 1 ≤ N := le_trans (by norm_num) (hN₀.trans hN)
  simpa only [one_mul] using h N 1 K hN le_rfl (Real.one_le_rpow hN1 hε.le) hK hKbound

/-- This is the full original mass-packing clause used by `RawSupport`.
Its lower bound is the actual (possibly half-pruned) saturation floor. -/
theorem raw_mass_packing_of_power_bounds {J : ℕ} (I : Finset (Fin J))
    (mass : Fin J → ENNReal) {N K C A a b ζ H : ℝ} (P : ℕ)
    (hN : 1 ≤ N) (hK : 0 < K) (hA : 0 < A)
    (hpoly : C * K ^ (P + 1) ≤ N ^ ζ) (hexp : a + ζ ≤ b + H)
    (hfloor : ∀ e ∈ I, ENNReal.ofReal (N ^ b * A / K) ≤ mass e)
    (hupper : (∑ e ∈ I, mass e) ≤ ENNReal.ofReal (C * K ^ P * N ^ a * A)) :
    ∃ v : ℝ, 0 < v ∧ (∀ e ∈ I, ENNReal.ofReal v ≤ mass e) ∧
      (∑ e ∈ I, mass e) ≤ ENNReal.ofReal (v * N ^ H) := by
  refine ⟨N ^ b * A / K, by positivity, hfloor, ?_⟩
  exact hupper.trans (ENNReal.ofReal_le_ofReal
    (packing_power_ratio P hN hK hA.le hpoly hexp))

/-- One small allowance pays every numerical cost of full witness packing,
uniformly in the physical width, block length and absolute profile shift. -/
theorem exists_raw_packing_allowance {χ : ℝ} (hχ : 0 < χ) :
    ∃ ε N₀ : ℝ, 0 < ε ∧ 2 ≤ N₀ ∧ ε ≤ χ / 32 ∧
      ∀ N K Δ H τ band u : ℝ, N₀ ≤ N → 1 ≤ K → K ≤ N ^ ε →
        Δ ≤ H + ε → τ ≤ ε → band ≤ ε → u ≤ ε →
        2097152 * Real.pi * K ^ (8 + 1) ≤ N ^ (χ / 2) ∧
          Δ + τ + 4 * band + 2 * u + χ / 2 ≤ H + χ := by
  obtain ⟨ε₀, N₀, hε₀, hN₀, hpoly⟩ :=
    exists_packing_polynomial_allowance (2097152 * Real.pi) (by positivity) 8
      (by positivity : 0 < χ / 2)
  let ε := min ε₀ (χ / 32)
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεsmall : ε ≤ χ / 32 := min_le_right _ _
  refine ⟨ε, N₀, hε, hN₀, hεsmall, ?_⟩
  intro N K Δ H τ band u hN hK hKN hΔ hτ hband hu
  have hN1 : 1 ≤ N := le_trans (by norm_num) (hN₀.trans hN)
  refine ⟨hpoly N K hN hK (hKN.trans ?_), by linarith⟩
  exact Real.rpow_le_rpow_of_exponent_le hN1 (min_le_left _ _)

/-- The packing allowance applies on the same source sequence as soon as its
actual slack is subpower. No independent frequent subsequence is selected. -/
theorem eventually_raw_packing_allowance {χ : ℝ} (hχ : 0 < χ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ χ / 32 ∧
      ∀ (N K : ℕ → ℝ), Filter.Tendsto N Filter.atTop Filter.atTop →
        (∀ j, 1 ≤ K j) →
        (∀ a : ℝ, 0 < a → ∀ᶠ j in Filter.atTop, K j ≤ N j ^ a) →
        ∀ Δ H τ band u : ℝ, Δ ≤ H + ε → τ ≤ ε → band ≤ ε → u ≤ ε →
          ∀ᶠ j in Filter.atTop,
            2097152 * Real.pi * K j ^ (8 + 1) ≤ N j ^ (χ / 2) ∧
              Δ + τ + 4 * band + 2 * u + χ / 2 ≤ H + χ := by
  obtain ⟨ε, N₀, hε, hN₀, hεχ, h⟩ := exists_raw_packing_allowance hχ
  refine ⟨ε, hε, hεχ, ?_⟩
  intro N K hN hK hsub Δ H τ band u hΔ hτ hband hu
  filter_upwards [hN.eventually_ge_atTop N₀, hsub ε hε] with j hNj hKj
  exact h (N j) (K j) Δ H τ band u hNj (hK j) hKj hΔ hτ hband hu

end
end Submission.Obl.k4_raw_localized_native_systems.Packing
