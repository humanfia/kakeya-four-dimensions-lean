/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarHierarchyPowers.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarHierarchyPowers.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Explicit scale exponents for the scalar first-jet hierarchy. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

theorem scalar_hierarchy_link_bound {H h B K : ℝ}
    (hH : 0 < H) (hh : 0 < h) (hhH : h ≤ H)
    (hB : 0 ≤ B) (hK : 0 < K) (hlower : H ^ (33 / 32 : ℝ) / 2 ≤ h) :
    4 * (B * H ^ (5 / 4 : ℝ) + B * h ^ (5 / 4 : ℝ)) / (h / K) ≤
      16 * B * K * H ^ (7 / 32 : ℝ) := by
  have hpow : h ^ (5 / 4 : ℝ) ≤ H ^ (5 / 4 : ℝ) :=
    Real.rpow_le_rpow hh.le hhH (by norm_num)
  have he : H ^ (5 / 4 : ℝ) = H ^ (7 / 32 : ℝ) * H ^ (33 / 32 : ℝ) := by
    rw [← Real.rpow_add hH]
    norm_num
  calc
    _ = (4 * K * (B * H ^ (5 / 4 : ℝ) + B * h ^ (5 / 4 : ℝ))) / h := by field_simp <;> ring
    _ ≤ (4 * K * (2 * B * H ^ (5 / 4 : ℝ))) / h := by
      apply div_le_div_of_nonneg_right _ hh.le
      exact mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left hpow hB]) (by positivity)
    _ ≤ _ := by
      apply (div_le_iff₀ hh).mpr
      calc
        _ = (16 * B * K * H ^ (7 / 32 : ℝ)) * (H ^ (33 / 32 : ℝ) / 2) := by rw [he]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlower (by positivity)

theorem scalar_hierarchy_taylor_bound {H B C distance : ℝ}
    (hH : 0 < H) (hH1 : H ≤ 1) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hdistance : distance ≤ H) :
    2 * B * H ^ (5 / 4 : ℝ) + distance * (C * H ^ (7 / 32 : ℝ)) ≤
      (2 * B + C) * H ^ (11 / 10 : ℝ) := by
  have hp : H ^ (5 / 4 : ℝ) ≤ H ^ (11 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hH hH1 (by norm_num)
  have hq : H * H ^ (7 / 32 : ℝ) ≤ H ^ (11 / 10 : ℝ) := by
    calc
      _ = H ^ (1 : ℝ) * H ^ (7 / 32 : ℝ) := by rw [Real.rpow_one]
      _ = H ^ (1 + 7 / 32 : ℝ) := (Real.rpow_add hH _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hH hH1 (by norm_num)
  have h₁ := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * B by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hdistance (show 0 ≤ C * H ^ (7 / 32 : ℝ) by positivity)
  have h₃ := mul_le_mul_of_nonneg_left hq hC
  nlinarith

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
