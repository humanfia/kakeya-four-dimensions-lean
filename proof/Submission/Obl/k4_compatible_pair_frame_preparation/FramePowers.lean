import Mathlib

namespace Submission.Obl.k4_compatible_pair_frame_preparation

open Filter

/-- A common subpower slack for the rounded frames and copied lists. -/
noncomputable def frameSlack (κ : ℝ) : ℝ := (2 : ℝ) ^ 100 * κ ^ 5

theorem frameSlack_one {κ : ℝ} (hκ : 1 ≤ κ) : 1 ≤ frameSlack κ := by
  have hc : (1 : ℝ) ≤ 2 ^ 100 := by norm_num
  have hk : (1 : ℝ) ≤ κ ^ 5 := one_le_pow₀ hκ
  simpa only [one_mul, frameSlack] using mul_le_mul hc hk (by norm_num : (0 : ℝ) ≤ 1) (by positivity)

theorem frameSlack_input {κ : ℝ} (hκ : 1 ≤ κ) : κ ≤ frameSlack κ := by
  have hp : κ ≤ κ ^ 5 := by simpa only [pow_one] using pow_le_pow_right₀ hκ (show 1 ≤ 5 by omega)
  exact hp.trans (le_mul_of_one_le_left (by positivity) (by norm_num : (1 : ℝ) ≤ 2 ^ 100))

theorem frameSlack_two {κ : ℝ} (hκ : 1 ≤ κ) : 2 ≤ frameSlack κ := by
  have hp : 1 ≤ κ ^ 5 := one_le_pow₀ hκ
  calc
    2 ≤ (2 : ℝ) ^ 100 := by norm_num
    _ ≤ frameSlack κ := le_mul_of_one_le_right (by positivity) hp

theorem frameSlack_matrix {κ : ℝ} (hκ : 1 ≤ κ) :
    632 * (4 * κ) ^ 2 ≤ frameSlack κ := by
  have hk : κ ^ 2 ≤ κ ^ 5 := pow_le_pow_right₀ hκ (by omega)
  calc
    632 * (4 * κ) ^ 2 = 10112 * κ ^ 2 := by ring
    _ ≤ (2 : ℝ) ^ 100 * κ ^ 2 :=
      mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg κ)
    _ ≤ frameSlack κ := mul_le_mul_of_nonneg_left hk (by positivity)

theorem frame_neighbour_radius {κ : ℝ} (hκ : 1 ≤ κ) :
    (⌈2 * (78 * (4 * κ)) + 1⌉₊ : ℝ) ≤ 626 * κ := by
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * (78 * (4 * κ)) + 1 by linarith)
  linarith

theorem frameSlack_lists {κ : ℝ} (hκ : 1 ≤ κ) :
    κ * ((98 * (2 * ⌈2 * (78 * (4 * κ)) + 1⌉₊ + 1) ^ 4 + 1 : ℕ) : ℝ) ≤
      frameSlack κ := by
  have hc := frame_neighbour_radius hκ
  have hκ0 : 0 ≤ κ := by linarith
  have hpow : (2 * (⌈2 * (78 * (4 * κ)) + 1⌉₊ : ℝ) + 1) ^ 4 ≤ (1253 * κ) ^ 4 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hκ4 : 1 ≤ κ ^ 4 := one_le_pow₀ hκ
  have hmult : ((98 * (2 * ⌈2 * (78 * (4 * κ)) + 1⌉₊ + 1) ^ 4 + 1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ 100 * κ ^ 4 := by
    push_cast
    calc
      98 * (2 * (⌈2 * (78 * (4 * κ)) + 1⌉₊ : ℝ) + 1) ^ 4 + 1 ≤
          98 * (1253 * κ) ^ 4 + κ ^ 4 := by gcongr
      _ = (98 * 1253 ^ 4 + 1) * κ ^ 4 := by ring
      _ ≤ (2 : ℝ) ^ 100 * κ ^ 4 :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  unfold frameSlack
  calc κ * _ ≤ κ * ((2 : ℝ) ^ 100 * κ ^ 4) := mul_le_mul_of_nonneg_left hmult hκ0
    _ = _ := by ring

/-- A real size threshold absorbs the fixed frame-slack constant. -/
theorem frameSlack_le_rpow {N κ ε : ℝ} (hN : 0 < N) (hκ : 0 ≤ κ)
    (hκle : κ ≤ N ^ (ε / 10)) (hlarge : (2 : ℝ) ^ 100 ≤ N ^ (ε / 2)) :
    frameSlack κ ≤ N ^ ε := by
  calc
    frameSlack κ ≤ N ^ (ε / 2) * (N ^ (ε / 10)) ^ 5 := by
      exact mul_le_mul hlarge (pow_le_pow_left₀ hκ hκle 5) (by positivity)
        (Real.rpow_nonneg hN.le _)
    _ = N ^ ε := by
      rw [← Real.rpow_mul_natCast hN.le, ← Real.rpow_add hN]
      congr 1
      norm_num
      ring

/-- A fixed fifth-power enlargement still fits any prescribed asymptotic slack. -/
theorem eventually_frameSlack {N : ℕ → ℝ} (hN : Filter.Tendsto N atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ κ : ℝ, 1 ≤ κ → κ ≤ N k ^ (ε / 10) →
      frameSlack κ ≤ N k ^ ε := by
  have hg : Filter.Tendsto (fun k => N k ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hN
  filter_upwards [hg.eventually (eventually_ge_atTop ((2 : ℝ) ^ 100)),
    hN.eventually (eventually_ge_atTop 1)] with k hk hNk
  intro κ hκ hκle
  exact frameSlack_le_rpow (by linarith) (by linarith) hκle hk

end Submission.Obl.k4_compatible_pair_frame_preparation
