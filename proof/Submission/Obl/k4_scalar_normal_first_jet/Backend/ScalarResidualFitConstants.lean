/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarResidualFitConstants.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarResidualFitConstants.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarBlockFitConstants

/-! The same polynomial budget bounds every actual residual-group input. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

theorem scalarBlockFitBound_dominates {K c : ℝ} {m : ℕ} (hK : 1 ≤ K)
    (hc : 0 ≤ c) (hcupper : c ≤ 100000) (hm : m ≤ 10) :
    c * K ^ m ≤ scalarBlockFitBound K := by
  calc
    _ ≤ c * K ^ 10 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK hm) hc
    _ ≤ 100000 * K ^ 10 := mul_le_mul_of_nonneg_right hcupper (by positivity)
    _ = _ := rfl

theorem scalarBlockFitBound_residual_bounds {K : ℝ} (hK : 1 ≤ K) :
    1200 * K ^ 4 ≤ scalarBlockFitBound K ∧
    23 * K ^ 2 ≤ scalarBlockFitBound K ∧
    7 * K ≤ scalarBlockFitBound K ∧
    20000 * K ^ 6 ≤ scalarBlockFitBound K := by
  refine ⟨scalarBlockFitBound_dominates hK (by norm_num) (by norm_num) (by norm_num),
    scalarBlockFitBound_dominates hK (by norm_num) (by norm_num) (by norm_num), ?_,
    scalarBlockFitBound_dominates hK (by norm_num) (by norm_num) (by norm_num)⟩
  simpa only [pow_one] using
    (scalarBlockFitBound_dominates (m := 1) (c := 7) hK (by norm_num) (by norm_num) (by norm_num))

theorem scalarBlockFitBound_starting_bin_budget {K : ℝ} (hK : 1 ≤ K) :
    (10000 * K ^ 4) / scalarBlockFitBound K ≤ (K⁻¹) ^ 2 / 2 := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hBpos : 0 < scalarBlockFitBound K := zero_lt_one.trans_le (scalarBlockFitBound_bounds hK).1
  apply (div_le_iff₀ hBpos).mpr
  have hh := mul_le_mul_of_nonneg_left (scalarBlockFitBound_residual_bounds hK).2.2.2
    (show 0 ≤ (K⁻¹) ^ 2 / 2 by positivity)
  have he : (K⁻¹) ^ 2 / 2 * (20000 * K ^ 6) = 10000 * K ^ 4 := by field_simp; ring
  simpa only [he] using hh

theorem scalar_residual_density_identity {K ρ : ℝ} (hK : 0 < K) :
    (ρ / (10000 * K ^ 4)) * ((K⁻¹) ^ 2 / 2) = ρ / (20000 * K ^ 6) := by
  field_simp
  ring

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
