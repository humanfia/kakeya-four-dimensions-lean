import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedSliceDensities

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ComparisonBandFactors.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The fixed original-band cap is dominated by the common comparison
density times the fine original prior, at the actual queried thickness. -/
theorem original_band_factor {K H J a W d : ℝ} (hH : 1 ≤ H) (hJ : 0 ≤ J)
    (ha : 0 < a) (hW : 0 < W) (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    16800 * K ^ 2 * J * (3 * W) ^ d ≤
      (34406400 * K ^ 2 * H ^ d) * (J * a ^ d) * (W / a) ^ d := by
  have hthree : (3 : ℝ) ^ d ≤ 3 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hd1
  have hHp : 1 ≤ H ^ d := Real.one_le_rpow hH hd
  have hcancel : a ^ d * (W / a) ^ d = W ^ d := by
    rw [← Real.mul_rpow ha.le (div_nonneg hW.le ha.le)]
    congr 1
    field_simp
  calc
    _ = 16800 * K ^ 2 * J * (3 : ℝ) ^ d * W ^ d := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hW.le]
      ring
    _ ≤ 16800 * K ^ 2 * J * 3 * W ^ d := by gcongr
    _ = 50400 * (K ^ 2 * J * W ^ d) := by ring
    _ ≤ (34406400 * H ^ d) * (K ^ 2 * J * W ^ d) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ = _ := by rw [← hcancel]; ring

namespace ProjectedLayer

variable {α : Type} [MeasurableSpace α]

/-- The whole-band ceiling uses the fine thickness in its prior even when
the queried polynomial belongs to the coarse color. -/
theorem comparisonBand_factor (A : ProjectedLayer α) (p : Parent α) (hbase : p.Basic)
    {k : ℕ} {sf m H h b W : ℝ} (hN : 0 < p.N k) (hH : 1 ≤ H)
    (hh : 0 < h) (hb : 0 < b) (hW : 0 < W) (hd : 0 ≤ p.d) (hd1 : p.d ≤ 1)
    {D : Fin A.count → Finset (ℤ × ℤ × ℤ)} (e : SliceIndex D)
    (hπ : 0 < p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = A.tag e.1 0}) :
    ENNReal.ofReal (16800 * p.K k ^ 2 * p.N k ^ (-m) * h * b * (3 * W) ^ p.d) *
      p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = A.tag e.1 0} ≤
      ENNReal.ofReal (p.projectedComparisonDensity k H *
        p.comparisonPrior k sf m h b (some (A.sliceComparisonCode e)) *
          (W / p.N k ^ (-sf)) ^ p.d) := by
  letI := (hbase k).2.2.1
  have hn := Real.rpow_pos_of_pos hN (-m)
  have ha := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hN (-sf)) p.d
  have hπtop := measure_ne_top (p.π k) {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = A.tag e.1 0}
  have hleft : ENNReal.ofReal (16800 * p.K k ^ 2 * p.N k ^ (-m) * h * b * (3 * W) ^ p.d) *
      p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = A.tag e.1 0} =
      ENNReal.ofReal ((16800 * p.K k ^ 2 * p.N k ^ (-m) * h * b * (3 * W) ^ p.d) *
        (p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = A.tag e.1 0}).toReal) := by
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤
      16800 * p.K k ^ 2 * p.N k ^ (-m) * h * b * (3 * W) ^ p.d),
      ENNReal.ofReal_toReal hπtop]
  have hprior : p.comparisonPrior k sf m h b (some (A.sliceComparisonCode e)) =
      (p.N k ^ (-m) * h * b * (p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = A.tag e.1 0}).toReal) *
        (p.N k ^ (-sf)) ^ p.d := by
    rw [A.comparisonPrior_slice_eq p hbase hN hh hb e hπ]
    unfold slicedWeight unscaledWeight
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (mul_nonneg hh.le hb.le),
      ENNReal.toReal_ofReal (mul_nonneg hn.le ha.le)]
    ring
  rw [hleft, hprior]
  apply ENNReal.ofReal_le_ofReal
  have hf := original_band_factor (K := p.K k) hH
    (show 0 ≤ p.N k ^ (-m) * h * b *
      (p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = A.tag e.1 0}).toReal by positivity)
    (Real.rpow_pos_of_pos hN (-sf)) hW hd hd1
  dsimp [Parent.projectedComparisonDensity]
  convert hf using 1 <;> ring

end ProjectedLayer
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
