import Submission.Obl.k4_raw_localized_native_systems.Window.RawLaws
import Submission.Obl.k4_finite_width_output_exclusion.ChartTransport

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open Submission.Obl.k4_finite_width_output_exclusion

/-- A small gap below the frozen depth pays the raw second derivative bound;
closeness of the depths pays the value bound. -/
theorem raw_test_slack_bounds {N κ r s χ ε : ℝ}
    (hN : 1 ≤ N) (hκ0 : 0 ≤ κ) (hκ : κ ≤ N ^ ε)
    (hgap : r + ε ≤ s) (hclose : s - r + 2 * ε ≤ 2 * χ)
    (htwo : 2 ≤ N ^ ε) :
    κ * δ N r ≤ N ^ χ * N ^ (-s + χ) ∧
      κ / δ N r ≤ N ^ χ / N ^ (-s + χ) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hδ := Submission.Obl.k4_finite_width_output_exclusion.delta_bounds hN0 r
  constructor
  · calc
      κ * δ N r ≤ N ^ ε * (2 * N ^ (-r)) :=
        mul_le_mul hκ hδ.2 (delta_pos N r).le (by positivity)
      _ ≤ N ^ ε * (N ^ ε * N ^ (-r)) := by gcongr
      _ = N ^ (2 * ε - r) := by rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; ring
      _ ≤ N ^ (-s + 2 * χ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ = N ^ χ * N ^ (-s + χ) := by rw [← Real.rpow_add hN0]; congr 1; ring
  · calc
      κ / δ N r ≤ N ^ ε / N ^ (-r) :=
        div_le_div₀ (by positivity) hκ (by positivity) hδ.1
      _ = N ^ (ε + r) := by rw [← Real.rpow_sub hN0]; congr 1; ring
      _ ≤ N ^ s := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ = N ^ χ / N ^ (-s + χ) := by rw [← Real.rpow_sub hN0]; congr 1; ring

end Submission.Obl.k4_raw_localized_native_systems.Window
