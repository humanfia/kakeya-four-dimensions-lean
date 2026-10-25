import Mathlib

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

noncomputable section

/-- The cap width may depend on the current index: the original caps are
uniform over their depth parameter. This chooses its exact power exponent. -/
def hiddenWindowExponent (N H s u : ℝ) : ℝ := s + u - Real.logb N (2 * H + 1)

/-- Subpower coarse coefficients enlarge the hidden window by at most two
subpower exponents, while its exact width is still an admissible power. -/
theorem hiddenWindowExponent_bounds {N H s u σ : ℝ} (hN : 1 < N)
    (hH : 1 ≤ H) (hHN : H ≤ N ^ σ) (hthree : 3 ≤ N ^ σ) :
    s + u - 2 * σ ≤ hiddenWindowExponent N H s u ∧
      hiddenWindowExponent N H s u ≤ s + u ∧
      N ^ (-s) * (2 * H + 1) * N ^ (-u) = N ^ (-hiddenWindowExponent N H s u) := by
  have hNp : 0 < N := zero_lt_one.trans hN
  have hHp : 0 < 2 * H + 1 := by linarith
  have hle : 2 * H + 1 ≤ N ^ (2 * σ) := by
    calc _ ≤ 3 * H := by linarith
      _ ≤ N ^ σ * N ^ σ := mul_le_mul hthree hHN (by linarith) (by positivity)
      _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring
  have hlog0 : 0 ≤ Real.logb N (2 * H + 1) := Real.logb_nonneg hN (by linarith)
  have hlog : Real.logb N (2 * H + 1) ≤ 2 * σ :=
    (Real.logb_le_iff_le_rpow hN hHp).mpr hle
  refine ⟨by dsimp [hiddenWindowExponent]; linarith,
    by dsimp [hiddenWindowExponent]; linarith, ?_⟩
  rw [show -hiddenWindowExponent N H s u = -s + Real.logb N (2 * H + 1) + -u by
    dsimp [hiddenWindowExponent]; ring,
    Real.rpow_add hNp, Real.rpow_add hNp, Real.rpow_logb hNp (ne_of_gt hN) hHp]

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
