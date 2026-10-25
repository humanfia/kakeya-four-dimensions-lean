/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarSlopeBudgets.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarSlopeBudgets.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Explicit polynomial losses in the residual-slope contradiction. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

theorem scalar_slope_collision_cost {p K τ η d γ j : ℝ}
    (hp : 0 < p) (hK : 1 ≤ K) (hτ : 0 < τ) (hη : 0 ≤ η) (hd : d ≤ 1) :
    (3 * (K * ((2 * K) / p) ^ d)) *
      (((η / τ) / (p ^ j * τ) * (K * p ^ (j + d))) * K +
        (2 * (p + 2 * (K * p)) / (p ^ γ)) * K ^ 2) ≤
      6 * K ^ 4 * η / τ ^ 2 + 36 * K ^ 5 * p ^ (1 - d - γ) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hpj : p ^ j ≠ 0 := (Real.rpow_pos_of_pos hp _).ne'
  have hpd : p ^ d ≠ 0 := (Real.rpow_pos_of_pos hp _).ne'
  have hpγ : p ^ γ ≠ 0 := (Real.rpow_pos_of_pos hp _).ne'
  have htwoK : 1 ≤ 2 * K := by linarith
  have hKd : (2 * K) ^ d ≤ 2 * K := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le htwoK hd
  have hpow : p ^ (1 - d - γ) = p / (p ^ d * p ^ γ) := by
    rw [Real.rpow_sub hp, Real.rpow_sub hp, Real.rpow_one]
    ring
  have heq : (3 * (K * ((2 * K) / p) ^ d)) *
      (((η / τ) / (p ^ j * τ) * (K * p ^ (j + d))) * K +
        (2 * (p + 2 * (K * p)) / (p ^ γ)) * K ^ 2) =
      3 * K ^ 3 * (2 * K) ^ d * η / τ ^ 2 +
        6 * K ^ 3 * (2 * K) ^ d * (1 + 2 * K) * p ^ (1 - d - γ) := by
    rw [Real.div_rpow (by positivity : 0 ≤ 2 * K) hp.le, Real.rpow_add hp, hpow]
    field_simp
    <;> ring
  rw [heq]
  apply add_le_add
  · calc
      _ ≤ 3 * K ^ 3 * (2 * K) * η / τ ^ 2 := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ 6 * K ^ 3 * (2 * K) * (3 * K) * p ^ (1 - d - γ) := by
        gcongr
        linarith
      _ = _ := by ring

theorem scalar_slope_pruning_cost {p K τ j V Jc : ℝ}
    (hp : 0 < p) (hK : 0 ≤ K) (hτ : 0 ≤ τ) (hV : V ≤ K)
    (hJ : Jc ≤ K * p ^ (-j)) :
    τ * V + (p ^ j * τ) * Jc ≤ 2 * K * τ := by
  have hcancel : p ^ j * p ^ (-j) = 1 := by rw [← Real.rpow_add hp]; simp
  calc
    _ ≤ τ * K + (p ^ j * τ) * (K * p ^ (-j)) := by gcongr
    _ = τ * K + K * τ * (p ^ j * p ^ (-j)) := by ring
    _ = 2 * K * τ := by rw [hcancel]; ring

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
