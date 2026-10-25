import Submission.Obl.k4_wide_three_layer_scalar_inputs.ShortNumerics

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

/-- The explicit affine bound and graph errors used by x0879's
`Native.ShortBound` (LOT o250, commit525ce8d3), with original accuracies. -/
noncomputable def rawBlockBound (H K q a : ℝ) : ℝ := 12 * (2 * H) ^ 2 * (K * (1 + a / q ^ 2))

noncomputable def rawBlockError (H K q a χ ζ : ℝ) : ℝ :=
  K + rawBlockBound H K q a * (2 * χ + q * (ζ + χ)) / a

noncomputable def rawSheetError (P q a D χ ζ : ℝ) : ℝ :=
  (P * a + 7 * (160 * P) * (q * (ζ + χ)) / (4 * D)) / a

structure RawShortBudget (R H K q a g D χ ζ P : ℝ) : Prop where
  affine_bound : rawBlockBound H K q a ≤ R ^ 5
  block_tolerance : 1 ≤ rawBlockError H K q a χ ζ ∧ rawBlockError H K q a χ ζ ≤ 2 * H
  sheet_tolerance : 1 ≤ rawSheetError P q a D χ ζ ∧ rawSheetError P q a D χ ζ ≤ 2 * H
  block_coeff : 8 * (rawBlockBound H K q a * (2 + 4 * (4 * H) + 3 * (q * g)) / a) ≤ R ^ 10
  sheet_coeff : 8 * (11 * (160 * P) / a) ≤ R ^ 10

/-- The literal native/projected error expressions fit the same matching
budget. In particular their tolerances remain at least one, as required
when scaling the finest-cell variation estimate. -/
theorem rawShortBudget_of_polynomial_budget {N R H K q a g D χ ζ P w mesh : ℝ}
    (hs : ShortNumerics N H q a g D χ ζ w mesh (R ^ 10) (R ^ 5) (4 * H))
    (hRbig : 10000 ≤ R) (hH : 1 ≤ H) (hHR : H ≤ R) (hH6 : H ^ 6 ≤ R)
    (hK : 1 ≤ K) (hKH : K ≤ H) (hq : 0 < q) (hg : 0 < g) (ha : 0 < a) (hD : 0 < D)
    (hqlo : 1 / R ^ 2 ≤ q) (halo : 1 / R ^ 2 ≤ a) (ha1 : a ≤ 1) (hD1 : D ≤ 1)
    (hχ : 0 ≤ χ) (hζ : 0 ≤ ζ) (hP : 1 ≤ P) (hPH : 160 * P ≤ H) :
    RawShortBudget R H K q a g D χ ζ P := by
  have hR : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hP0 : 0 ≤ P := by linarith
  have hPR : P ≤ H := by linarith
  have hqinv : q⁻¹ ≤ R ^ 2 := by
    have hh := inv_anti₀ (by positivity : 0 < 1 / R ^ 2) hqlo
    simpa using hh
  have hainv : a⁻¹ ≤ R ^ 2 := by
    have hh := inv_anti₀ (by positivity : 0 < 1 / R ^ 2) halo
    simpa using hh
  have haq : a / q ^ 2 ≤ R ^ 4 := by
    rw [div_eq_mul_inv, ← inv_pow]
    exact (mul_le_mul ha1 (pow_le_pow_left₀ (by positivity) hqinv 2) (by positivity) zero_le_one).trans
      (by ring_nf; rfl)
  have hR4 : 1 ≤ R ^ 4 := one_le_pow₀ hR
  have hH3 : 0 ≤ H ^ 3 := by positivity
  have h96 : 96 * H ^ 3 ≤ R := by
    have hh : (96 * H ^ 3) ^ 2 ≤ R ^ 2 := by
      calc _ = 9216 * H ^ 6 := by ring
        _ ≤ 9216 * R := by gcongr
        _ ≤ R ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right (show 9216 ≤ R by linarith) hR0.le]
    nlinarith
  have hLb : rawBlockBound H K q a ≤ R ^ 5 := by
    unfold rawBlockBound
    calc 12 * (2 * H) ^ 2 * (K * (1 + a / q ^ 2)) =
          48 * H ^ 2 * K * (1 + a / q ^ 2) := by ring
      _ ≤ 48 * H ^ 2 * H * (2 * R ^ 4) := by gcongr; linarith
      _ = (96 * H ^ 3) * R ^ 4 := by ring
      _ ≤ R * R ^ 4 := mul_le_mul_of_nonneg_right h96 (by positivity)
      _ = R ^ 5 := by ring
  have hLb0 : 0 ≤ rawBlockBound H K q a := by unfold rawBlockBound; positivity
  have hnoise : 0 ≤ 2 * χ + q * (ζ + χ) := by positivity
  have hblock : rawBlockBound H K q a * (2 * χ + q * (ζ + χ)) ≤ H * a :=
    (mul_le_mul_of_nonneg_right hLb hnoise).trans hs.block_graph
  have hsheet : 7 * (160 * P) * (q * (ζ + χ)) / (4 * D) ≤ H * a := by
    apply le_trans _ hs.sheet_graph
    gcongr
  have hsheet0 : 0 ≤ 7 * (160 * P) * (q * (ζ + χ)) / (4 * D) := by positivity
  refine ⟨hLb, ?_, ?_, ?_, ?_⟩
  · unfold rawBlockError
    constructor
    · exact hK.trans (le_add_of_nonneg_right (div_nonneg (mul_nonneg hLb0 hnoise) ha.le))
    · have hh : rawBlockBound H K q a * (2 * χ + q * (ζ + χ)) / a ≤ H :=
        (div_le_iff₀ ha).mpr hblock
      linarith
  · unfold rawSheetError
    constructor
    · rw [le_div_iff₀ ha]
      nlinarith
    · rw [div_le_iff₀ ha]
      nlinarith [mul_le_mul_of_nonneg_right hPR ha.le]
  · have hm : q * g ≤ 1 := hs.m_D.trans hD1
    have hdomain : 2 + 4 * (4 * H) + 3 * (q * g) ≤ 21 * R := by nlinarith
    calc 8 * (rawBlockBound H K q a * (2 + 4 * (4 * H) + 3 * (q * g)) / a)
          ≤ 8 * (R ^ 5 * (21 * R) * R ^ 2) := by
            rw [div_eq_mul_inv]
            gcongr <;> positivity
      _ = 168 * R ^ 8 := by ring
      _ ≤ R ^ 10 := by
        have hh : 168 ≤ R ^ 2 := (show 168 ≤ R by linarith).trans
          (by simpa using pow_le_pow_right₀ hR (show 1 ≤ 2 by norm_num))
        nlinarith only [mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ R ^ 8)]
  · apply le_trans _ hs.sheet_coeff
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hPH (show 0 ≤ (88 : ℝ) by norm_num)) ha.le
    convert hh using 1 <;> ring

end Submission.Obl.k4_wide_three_layer_scalar_inputs
