/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarFirstJetNumerics.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarFirstJetNumerics.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarDyadicPowerRanges

/-! Numerical transport from a designated first-jet row to the common final row. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

/-- The bridge slope error has a strictly better mesh exponent than
the required first-jet reading, so its centers need not change. -/
theorem scalar_first_jet_reading_transport {d H C Y R A A' y v : ℝ}
    (hd : 0 ≤ d) (hH : 0 < H) (hH1 : H ≤ 1) (hC : 0 ≤ C) (hY : 0 ≤ Y)
    (hread : |R - A * y - v| ≤ H ^ ((1 - d) / 32))
    (hslope : |A - A'| ≤ C * H ^ (7 / 32 : ℝ)) (hy : |y| ≤ Y) :
    |R - A' * y - v| ≤ (1 + C * Y) * H ^ ((1 - d) / 32) := by
  have hp : H ^ (7 / 32 : ℝ) ≤ H ^ ((1 - d) / 32) :=
    Real.rpow_le_rpow_of_exponent_ge hH hH1 (by linarith)
  have hproduct : |(A - A') * y| ≤ C * H ^ (7 / 32 : ℝ) * Y := by
    rw [abs_mul]
    exact mul_le_mul hslope hy (abs_nonneg _) (by positivity)
  calc
    _ = |(R - A * y - v) + (A - A') * y| := by congr 1; ring
    _ ≤ |R - A * y - v| + |(A - A') * y| := abs_add_le _ _
    _ ≤ H ^ ((1 - d) / 32) + C * H ^ (7 / 32 : ℝ) * Y := add_le_add hread hproduct
    _ ≤ H ^ ((1 - d) / 32) + C * H ^ ((1 - d) / 32) * Y := by gcongr
    _ = _ := by ring

/-- A coarse reading needs no geometric selection: the whole bounded
first jet fits in one interval when its scale is at least `1/K`. -/
theorem scalar_first_jet_coarse_reading {d H K B : ℝ}
    (hd : 0 ≤ d) (hK : 1 ≤ K) (hH : 1 / K ≤ H) (hH1 : H ≤ 1)
    (hbudget : 4 * K ^ 3 ≤ B) : 4 * K ^ 2 ≤ B * H ^ ((1 - d) / 32) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hHpos : 0 < H := (one_div_pos.mpr hKpos).trans_le hH
  have hB : 0 ≤ B := (by positivity : 0 ≤ 4 * K ^ 3).trans hbudget
  have hp : H ≤ H ^ ((1 - d) / 32) :=
    Real.self_le_rpow_of_le_one hHpos.le hH1 (by linarith)
  calc
    _ ≤ B / K := (le_div_iff₀ hKpos).mpr (by nlinarith only [hbudget])
    _ = B * (1 / K) := by ring
    _ ≤ B * H ^ ((1 - d) / 32) := mul_le_mul_of_nonneg_left (hH.trans hp) hB

/-- The same coarse-scale budget also absorbs the bounded row's
whole-cell Taylor error with the zero Taylor row. -/
theorem scalar_first_jet_coarse_taylor {H K B : ℝ}
    (hK : 1 ≤ K) (hH : 1 / K ≤ H) (hH1 : H ≤ 1) (hbudget : 4 * K ^ 3 ≤ B) :
    2 * K ≤ B * H ^ (11 / 10 : ℝ) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hHpos : 0 < H := (one_div_pos.mpr hKpos).trans_le hH
  have hB : 0 ≤ B := (by positivity : 0 ≤ 4 * K ^ 3).trans hbudget
  have hpower : H ^ (2 : ℕ) ≤ H ^ (11 / 10 : ℝ) := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hHpos hH1
      (by norm_num : (11 / 10 : ℝ) ≤ 2)
  calc
    _ ≤ 4 * K := by linarith
    _ ≤ B * (1 / K) ^ 2 := by
      rw [div_pow, one_pow, mul_one_div]
      exact (le_div_iff₀ (sq_pos_of_pos hKpos)).mpr (by nlinarith only [hbudget])
    _ ≤ B * H ^ 2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hH 2) hB
    _ ≤ _ := mul_le_mul_of_nonneg_left hpower hB

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
