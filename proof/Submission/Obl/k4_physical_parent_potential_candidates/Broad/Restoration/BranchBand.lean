-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/BranchBand.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/BranchBand.lean (session x0945).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_stable_quadratic_hidden_sheets.Sheet
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.AffineTransport

/-!
# Group lines lie in the tube of the branch

A point `(z, w)` of a group line has a small native fit `|a w² + B(z) w + C(z)| ≤ ε` (the old
native quadratic minus the potential and the common intercept), a hidden derivative
`2 a w + B(z)` of size between `A⁻¹` and `A`, and the sign of the selected branch. Then the
discriminant at `z` lies in the window of the accepted `real_branch_bounds`, and `w` is within
`ε A¹⁹` of the branch value `f z`.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

/-- The tube estimate for one point of a group line. -/
theorem band_of_native_fit {a ε A φ bu cu σ w : ℝ} (hA : 2 ≤ A) (hε : 0 < ε)
    (hroot : a * φ ^ 2 + bu * φ + cu = 0) (hsign : 0 < (2 * a * φ + bu) * σ)
    (hfit : |a * w ^ 2 + bu * w + cu| ≤ ε) (hwsign : 0 < (2 * a * w + bu) * σ)
    (hlo : A⁻¹ ≤ |2 * a * w + bu|) (hhi : |2 * a * w + bu| ≤ A)
    (hsmall : 4 * |a| * ε ≤ (2 * A ^ 2)⁻¹) :
    |w - φ| ≤ ε * A ^ 19 ∧ (A ^ 20)⁻¹ ≤ |2 * a * φ + bu| ∧ |2 * a * φ + bu| ≤ A ^ 20 := by
  have hA0 : 0 < A := by linarith
  -- the discriminant through the line point
  have hdisc : bu * bu - 4 * a * cu =
      (2 * a * w + bu) ^ 2 - 4 * a * (a * w ^ 2 + bu * w + cu) := by ring
  have hq2lo : (A⁻¹) ^ 2 ≤ (2 * a * w + bu) ^ 2 := by
    rw [← sq_abs (2 * a * w + bu)]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hA0.le) hlo 2
  have hq2hi : (2 * a * w + bu) ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs (2 * a * w + bu)]
    exact pow_le_pow_left₀ (abs_nonneg _) hhi 2
  have hcorr : |4 * a * (a * w ^ 2 + bu * w + cu)| ≤ (2 * A ^ 2)⁻¹ := by
    rw [abs_mul, abs_mul]
    calc |4| * |a| * |a * w ^ 2 + bu * w + cu| ≤ |4| * |a| * ε := by gcongr
      _ = 4 * |a| * ε := by norm_num
      _ ≤ (2 * A ^ 2)⁻¹ := hsmall
  have hcorr' := abs_le.mp hcorr
  have hAsq : (A⁻¹) ^ 2 = (A ^ 2)⁻¹ := by rw [inv_pow]
  have hhalf : (2 * A ^ 2)⁻¹ = (A ^ 2)⁻¹ / 2 := by
    rw [mul_inv, div_eq_mul_inv]; ring
  have hlow : 1 / (2 * A ^ 2) ≤ bu * bu - 4 * a * cu := by
    rw [hdisc, one_div]
    have : (2 * A ^ 2)⁻¹ ≤ (A ^ 2)⁻¹ - (2 * A ^ 2)⁻¹ := by rw [hhalf]; linarith
    linarith [hcorr'.1, hcorr'.2]
  have hupper : bu * bu - 4 * a * cu ≤ A ^ 2 + 1 := by
    rw [hdisc]
    have hsmall' : (2 * A ^ 2)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      nlinarith
    linarith [hcorr'.1, hcorr'.2]
  have hafit : 0 < ε / A := div_pos hε hA0
  obtain ⟨h1, h2, h3⟩ := Submission.Obl.k4_stable_quadratic_hidden_sheets.real_branch_bounds
    A (ε / A) a bu cu φ σ hA hafit hroot hsign hlow hupper
  refine ⟨?_, h1, h2⟩
  have hwfit : |a * w ^ 2 + bu * w + cu| ≤ ε / A * A := by
    rwa [div_mul_cancel₀ ε hA0.ne']
  have := h3 w hwfit hwsign
  calc |w - φ| ≤ ε / A * A ^ 20 := this
    _ = ε * A ^ 19 := by
      rw [div_mul_eq_mul_div, pow_succ, ← mul_assoc, mul_div_assoc, div_self hA0.ne', mul_one]

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
