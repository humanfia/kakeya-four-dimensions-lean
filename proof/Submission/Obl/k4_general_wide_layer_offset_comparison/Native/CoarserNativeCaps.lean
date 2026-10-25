-- Adapted from this LOT tree, obligation o254, branch x0898, commit f25a0cc9, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/CoarserNativeCaps.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0934, commit 3ef9d3b45123d3245f500a2dc2bd85270a8fff3d,
   Submission/Obl/k4_finite_projected_horizontal_candidates/CoarserNativeCaps.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_contact_equal_rate_affine_palettes.NativeCoarse

/-! Frozen exponent caps give the real-width caps used by sheet list counting. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Every real width between a frozen fine width and one is a frozen exponent
width in the same range. -/
theorem real_width_as_depth {N S R : ℝ} (hN : 1 < N)
    (hR : N ^ (-S) ≤ R) (hR1 : R ≤ 1) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ S ∧ N ^ (-s) = R := by
  have hN0 : 0 < N := zero_lt_one.trans hN
  have hR0 : 0 < R := (Real.rpow_pos_of_pos hN0 _).trans_le hR
  refine ⟨-Real.logb N R, neg_nonneg.mpr (Real.logb_nonpos hN hR0.le hR1), ?_, ?_⟩
  · have h := (Real.logb_le_logb hN (Real.rpow_pos_of_pos hN0 _) hR0).mpr hR
    rw [Real.logb_rpow hN0 hN.ne'] at h
    linarith
  · simpa only [neg_neg] using Real.rpow_logb hN0 hN.ne' hR0

/-- Coarser native caps at arbitrary positive real widths follow from the frozen
caps at exponent widths. Widths above one use the bounded original signal and
the accepted occupied-bin count, retaining the same original reference factor. -/
theorem coarser_native_bin_cap {Ω Q : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (code : Ω → Q) (signal : Ω → ℝ)
    {N S d H : ℝ} (hN : 1 < N) (hS : 0 ≤ S) (hd : 0 ≤ d) (hH : 0 ≤ H)
    (A : Q → ℝ≥0∞) (hbound : ∀ᵐ p ∂μ, |signal p| ≤ H)
    (hcap : ∀ s : ℝ, 0 ≤ s → s ≤ S → ∀ q j,
      μ {p | code p = q ∧ ⌊signal p / N ^ (-s)⌋ = j} ≤ ENNReal.ofReal ((N ^ (-s)) ^ d) * A q)
    {R : ℝ} (hR : N ^ (-S) ≤ R) (q : Q) (j : ℤ) :
    μ {p | code p = q ∧ ⌊signal p / R⌋ = j} ≤
      ENNReal.ofReal ((2 * H + 5) * R ^ d) * A q := by
  by_cases hR1 : R ≤ 1
  · obtain ⟨s, hs, hsS, hsR⟩ := real_width_as_depth hN hR hR1
    have h := hcap s hs hsS q j
    rw [hsR] at h
    refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    exact le_mul_of_one_le_left (Real.rpow_nonneg ((Real.rpow_pos_of_pos (zero_lt_one.trans hN) _).trans_le hR).le _)
      (by linarith)
  · have hR1' : 1 ≤ R := (lt_of_not_ge hR1).le
    have hbase : μ {p | code p = q} ≤ ENNReal.ofReal (2 * H + 5) * A q := by
      apply Submission.Obl.k4_contact_equal_rate_affine_palettes.native_scalar_bin_cap μ
        {p | code p = q} signal (a := 1) (by norm_num) hH (A q)
      · simpa only [mul_one] using hbound
      · intro z
        simpa only [neg_zero, Real.rpow_zero, Real.one_rpow, div_one, ENNReal.ofReal_one, one_mul,
          Set.mem_ofPred_eq]
          using hcap 0 le_rfl hS q z
    calc
      _ ≤ μ {p | code p = q} := measure_mono fun p hp => hp.1
      _ ≤ ENNReal.ofReal (2 * H + 5) * A q := hbase
      _ ≤ ENNReal.ofReal ((2 * H + 5) * R ^ d) * A q := by
        apply mul_le_mul' (ENNReal.ofReal_le_ofReal _) le_rfl
        exact le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hR1' hd)

/-- The coarser cap can be written using the same fine reference numerator used
by the comparison tables. -/
theorem fine_reference_scale {a R d : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    R ^ d = a ^ d * (R / a) ^ d := by
  rw [← Real.mul_rpow ha.le (div_nonneg hR ha.le), mul_div_cancel₀ _ ha.ne']

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
