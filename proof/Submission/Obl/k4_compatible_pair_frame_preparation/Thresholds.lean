import Submission.Obl.k4_compatible_pair_frame_preparation.FramePowers

namespace Submission.Obl.k4_compatible_pair_frame_preparation

open Filter

/-- One real size threshold supplies all slack budgets used by the finite construction. -/
theorem exists_sample_thresholds {a e ε : ℝ} (ha : 0 < a) (he : 0 < e) (hε : 0 < ε) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ ε ∧ ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      2 ≤ N ∧ (2 : ℝ) ^ 100 ≤ N ^ (a + e) ∧
      ∀ κ : ℝ, 1 ≤ κ → κ ≤ N ^ ε₀ →
        frameSlack κ ≤ N ^ ε ∧ frameSlack κ ≤ N ∧
          frameSlack κ ≤ N ^ (a + e) ∧ κ ≤ N ^ a := by
  let ρ := min ε (min 1 (min a (a + e)))
  have hρ : 0 < ρ := lt_min hε (lt_min (by norm_num) (lt_min ha (by linarith)))
  have hρε : ρ ≤ ε := min_le_left _ _
  have hρ1 : ρ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hρa : ρ ≤ a :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρt : ρ ≤ a + e :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlarge₁ : ∀ᶠ N : ℝ in atTop, (2 : ℝ) ^ 100 ≤ N ^ (ρ / 2) :=
    (tendsto_rpow_atTop (by linarith : 0 < ρ / 2)).eventually (eventually_ge_atTop _)
  have hlarge₂ : ∀ᶠ N : ℝ in atTop, (2 : ℝ) ^ 100 ≤ N ^ (a + e) :=
    (tendsto_rpow_atTop (by linarith : 0 < a + e)).eventually (eventually_ge_atTop _)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (hlarge₁.and hlarge₂)
  refine ⟨ρ / 10, by positivity, by linarith, max 2 N₀, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  obtain ⟨hconst, hX⟩ := hN₀ N ((le_max_right _ _).trans hN)
  refine ⟨hN2, hX, fun κ hκ hκle => ?_⟩
  have hb : frameSlack κ ≤ N ^ ρ := frameSlack_le_rpow hNpos
    (zero_le_one.trans hκ) hκle hconst
  refine ⟨hb.trans (Real.rpow_le_rpow_of_exponent_le hN1 hρε), ?_,
    hb.trans (Real.rpow_le_rpow_of_exponent_le hN1 hρt), ?_⟩
  · simpa only [Real.rpow_one] using hb.trans (Real.rpow_le_rpow_of_exponent_le hN1 hρ1)
  · exact (frameSlack_input hκ).trans (hb.trans (Real.rpow_le_rpow_of_exponent_le hN1 hρa))

end Submission.Obl.k4_compatible_pair_frame_preparation
