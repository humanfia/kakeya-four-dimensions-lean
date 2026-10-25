import Submission.Obl.k4_raw_localized_native_systems.Packing.HomogeneousCompatibility
import Submission.Obl.k4_profile_density_bounds.Asymptotics
import Submission.Obl.k4_profile_density_bounds.Common

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open Filter
open Submission.Obl.k4_finite_width_output_exclusion
open Pairing Packing

/-- The actual fixed relative width gain is small compared with the common
homogeneous width on any retained long earlier frame. -/
theorem relative_width_long_upper {N q g band a gC : ℝ}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} (hN : 1 ≤ N) (hq : 0 < q) (hg : 0 ≤ g)
    (hdet : |Q.det| ≤ q ^ 2 * g * N ^ (2 * band))
    (hmajor : q * N ^ (-a) ≤ ‖longCol Q‖)
    (hrel : gC ≤ minorWidth Q * q / N ^ (4 : ℕ)) :
    gC ≤ q ^ 2 * g * N ^ (2 * band + a) / N ^ (4 : ℕ) := by
  apply hrel.trans
  calc
    _ ≤ (q * g * N ^ (2 * band + a)) * q / N ^ (4 : ℕ) := by
      gcongr
      exact minor_width_power_bound hN hq hg hdet hmajor
    _ = _ := by ring

/-- A small major cutoff and a larger common angular tolerance pay the
pinning and short-major scales, without any cost depending on the width. -/
theorem long_scale_pinning {N κ q g band a loss gC : ℝ}
    (hN : 1 ≤ N) (hκ : 1 ≤ κ) (hq : 0 < q) (hq1 : q ≤ 1) (hg : 0 < g)
    (hloss : loss ≤ 4)
    (hcurrent : gC ≤ q ^ 2 * g * N ^ (2 * band + 4 * a) / N ^ (4 : ℕ))
    (hsmall : 16 * κ * N ^ (-4 * a) ≤ δ N a) :
    4 * (2 * (N ^ loss * gC) + 2 * κ * g * N ^ (2 * band + 4 * a)) /
        (g * N ^ (8 * a + 2 * band)) ≤ δ N a := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hθ : 0 < g * N ^ (8 * a + 2 * band) := by positivity
  have hq2 : q ^ 2 ≤ 1 := by nlinarith
  have hc : gC ≤ g * N ^ (2 * band + 4 * a - 4) := by
    apply hcurrent.trans
    calc
      _ ≤ g * N ^ (2 * band + 4 * a) / N ^ (4 : ℕ) := by
        gcongr
        exact (mul_le_mul_of_nonneg_right hq2 hg.le).trans_eq (one_mul g)
      _ = _ := by rw [← Real.rpow_natCast, mul_div_assoc, ← Real.rpow_sub hN0]; norm_num
  have he : N ^ (8 * a + 2 * band) * N ^ (-4 * a) = N ^ (2 * band + 4 * a) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  have hρ : 2 * (N ^ loss * gC) ≤
      2 * (g * N ^ (8 * a + 2 * band)) * N ^ (-4 * a) := by
    calc
      _ ≤ 2 * (N ^ loss * (g * N ^ (2 * band + 4 * a - 4))) := by gcongr
      _ = 2 * g * N ^ (loss + (2 * band + 4 * a - 4)) := by
        rw [Real.rpow_add hN0]; ring
      _ ≤ 2 * g * N ^ (4 * a + 2 * band) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hloss])) (by positivity)
      _ = 2 * g * (N ^ (8 * a + 2 * band) * N ^ (-4 * a)) := by rw [he]; congr 2 <;> ring
      _ = _ := by ring
  have hσ : 2 * κ * g * N ^ (2 * band + 4 * a) =
      2 * κ * (g * N ^ (8 * a + 2 * band)) * N ^ (-4 * a) := by
    calc
      _ = 2 * κ * g * (N ^ (8 * a + 2 * band) * N ^ (-4 * a)) := by rw [he]
      _ = _ := by ring
  have hκθ : (g * N ^ (8 * a + 2 * band)) * N ^ (-4 * a) ≤
      κ * ((g * N ^ (8 * a + 2 * band)) * N ^ (-4 * a)) :=
    le_mul_of_one_le_left (by positivity) hκ
  rw [div_le_iff₀ hθ]
  calc
    _ ≤ 4 * (2 * (g * N ^ (8 * a + 2 * band)) * N ^ (-4 * a) +
        2 * κ * (g * N ^ (8 * a + 2 * band)) * N ^ (-4 * a)) := by
      rw [hσ]
      gcongr
    _ ≤ (g * N ^ (8 * a + 2 * band)) * (16 * κ * N ^ (-4 * a)) := by
      nlinarith only [hκθ]
    _ ≤ (g * N ^ (8 * a + 2 * band)) * δ N a :=
      mul_le_mul_of_nonneg_left hsmall hθ.le
    _ = _ := by ring

theorem long_scale_short {N κ q a : ℝ} (hN : 0 ≤ N) (hq : q ≠ 0) (hκ : 0 ≤ κ)
    (hsmall : 16 * κ * N ^ (-4 * a) ≤ δ N a) :
    4 * κ / q * (q * N ^ (-4 * a)) ≤ δ N a := by
  calc
    _ = 4 * κ * N ^ (-4 * a) := by field_simp
    _ ≤ 16 * κ * N ^ (-4 * a) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hN _)
    _ ≤ _ := hsmall

/-- The one numerical pinning budget holds on the original source
subsequence for every positive small angular exponent. -/
theorem eventually_long_scale {N κ : ℕ → ℝ}
    (hN : ∀ n, 1 ≤ N n) (hNt : Tendsto N atTop atTop) (hκ : ∀ n, 1 ≤ κ n)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, κ n ≤ N n ^ ε)
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n in atTop, 16 * κ n * N n ^ (-4 * a) ≤ δ (N n) a := by
  have hh := k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hNt hκ hsub 1 (show -4 * a < -a by linarith) (by norm_num : (0 : ℝ) ≤ 16)
  filter_upwards [hh] with n hn
  apply le_trans (by simpa only [pow_one] using hn.le)
  exact (k4_profile_density_bounds.width_bounds
    (lt_of_lt_of_le zero_lt_one (hN n)) a).1

end Submission.Obl.k4_raw_localized_native_systems.Window
