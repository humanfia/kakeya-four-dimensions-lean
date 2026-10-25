import Submission.Lib.K4OriginalStatePreparation.Numerics
import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedSliceDensities

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/WideComparisonNumerics.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory

noncomputable section

/-- At the prescribed wide comparison scale, the fine original thickness
factor remains strictly subcritical. -/
theorem wide_comparison_prior_factor {N H sc gain u R d : ℝ}
    (hN : 1 ≤ N) (hH : 1 ≤ H) (hd : 0 ≤ d) (hd1 : d < 1)
    (hu : 0 < u) (hgain : gain ≤ u) (hsmall : 4 * H ≤ N ^ u)
    (hR : N ^ (10 / (1 - d) * u) ≤ R) :
    (4 * H * N ^ (-sc) * R / N ^ (-sc - gain)) ^ d ≤ 2 * R ^ ((1 + d) / 2) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hRp : 0 < R := (Real.rpow_pos_of_pos hNp _).trans_le hR
  have hf : 0 < N ^ (-sc - gain) := Real.rpow_pos_of_pos hNp _
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hbase : 0 ≤ 4 * H * N ^ gain := by positivity
  have hbase_upper : 4 * H * N ^ gain ≤ N ^ (2 * u) := by
    calc
      _ ≤ N ^ u * N ^ u := mul_le_mul hsmall
        (Real.rpow_le_rpow_of_exponent_le hN hgain) (Real.rpow_nonneg hNp.le _) (by positivity)
      _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring
  have hcancel : N ^ gain * N ^ (-sc - gain) = N ^ (-sc) := by
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  have hratio : 4 * H * N ^ (-sc) * R / N ^ (-sc - gain) = R * (4 * H * N ^ gain) := by
    rw [← hcancel]
    field_simp
  rw [hratio, Real.mul_rpow hRp.le hbase]
  calc
    _ ≤ R ^ d * (N ^ (2 * u)) ^ d :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hbase hbase_upper hd) (by positivity)
    _ = R ^ d * N ^ (2 * u * d) := by rw [← Real.rpow_mul hNp.le]
    _ ≤ R ^ d * N ^ (d * u + 4 * u) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hRp.le _)
      apply Real.rpow_le_rpow_of_exponent_le hN
      have hdu := mul_le_mul_of_nonneg_right hd1.le hu.le
      linarith
    _ ≤ R ^ ((1 + d) / 2) :=
      Submission.Lib.K4OriginalStatePreparation.wide_jet_power_bound hN hd1 hu hR
    _ ≤ 2 * R ^ ((1 + d) / 2) := by nlinarith [Real.rpow_nonneg hRp.le ((1 + d) / 2)]

/-- All density and two-color reference factors are bounded by one sixth
power of the common loss parameter, with an absolute constant. -/
theorem comparison_density_budget {K H d : ℝ} (hK : 0 ≤ K) (hKH : K ≤ H)
    (hH : 1 ≤ H) (hd1 : d ≤ 1) :
    (34406400 * K ^ 2 * H ^ d) * (3 * (1 + 240 * H ^ 3)) ≤
      25000000000 * H ^ 6 := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hHd : H ^ d ≤ H := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hH hd1
  have hKsq : K ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ hK hKH _
  have hden : 34406400 * K ^ 2 * H ^ d ≤ 34406400 * H ^ 3 := by
    calc
      _ ≤ 34406400 * H ^ 2 * H := by gcongr
      _ = _ := by ring
  have hHp : 1 ≤ H ^ 3 := one_le_pow₀ hH
  have hbudget : 3 * (1 + 240 * H ^ 3) ≤ 723 * H ^ 3 := by linarith
  calc
    _ ≤ (34406400 * H ^ 3) * (723 * H ^ 3) :=
      mul_le_mul hden hbudget (by positivity) (by positivity)
    _ = 24875827200 * H ^ 6 := by ring
    _ ≤ _ := by gcongr <;> norm_num

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
