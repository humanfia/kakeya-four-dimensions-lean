/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/SaturationNumerics.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/SaturationNumerics.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.PruningNumerics

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

theorem crossingFactor_fourth_power_bound {κ : ℝ} (hκ : 1 ≤ κ) :
    crossingFactor κ ≤ 40 * Real.pi * κ ^ 4 := by
  have hsq : 1 ≤ κ ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right (by linarith : 1 + 4 * κ ^ 2 ≤ 5 * κ ^ 2)
    (show 0 ≤ 8 * Real.pi * κ ^ 2 by positivity)
  unfold crossingFactor
  nlinarith

theorem saturated_prior_factor_bound {N κ σ v τ f : ℝ} (hN : 0 < N)
    (hκ : 1 ≤ κ) (hκN : κ ≤ N ^ σ) :
    2 * N ^ v * N ^ (-f + τ) * crossingFactor κ ≤
      (80 * Real.pi * N ^ (v + τ + 4 * σ)) * N ^ (-f) := by
  have hκpow : κ ^ 4 ≤ N ^ (4 * σ) := by
    calc
      _ ≤ (N ^ σ) ^ 4 := pow_le_pow_left₀ (by linarith) hκN 4
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; congr 1; ring
  have hC : crossingFactor κ ≤ 40 * Real.pi * N ^ (4 * σ) :=
    (crossingFactor_fourth_power_bound hκ).trans
      (mul_le_mul_of_nonneg_left hκpow (by positivity))
  calc
    _ ≤ 2 * N ^ v * N ^ (-f + τ) * (40 * Real.pi * N ^ (4 * σ)) :=
      mul_le_mul_of_nonneg_left hC (by positivity)
    _ = _ := by simp_rw [Real.rpow_add hN]; ring

theorem saturation_loss_small {N κ σ τ u v c : ℝ} (hN : 0 < N) (hκ : 1 ≤ κ)
    (hκN : κ ≤ N ^ σ) (hbad : 24 * N ^ (-c) ≤ N ^ (-σ))
    (hcost : 480 * Real.pi * N ^ (5 * σ + τ - u) ≤ N ^ (-σ))
    (hlight : 6 * N ^ (-v) ≤ N ^ (-σ)) :
    4 * N ^ (-c) + 80 * Real.pi * N ^ (5 * σ + τ - u) + N ^ (-v) ≤ (2 * κ)⁻¹ := by
  have hκ0 : 0 < κ := by linarith
  have hi : N ^ (-σ) ≤ κ⁻¹ := by
    rw [Real.rpow_neg hN.le]
    exact inv_anti₀ hκ0 hκN
  rw [show (2 * κ)⁻¹ = κ⁻¹ / 2 by field_simp]
  nlinarith

end Submission.Obl.k4_balanced_native_packet_transport.CPF
