-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.RenewalCellScale, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/RenewalCellScale.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/RenewalCellScale.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit b13a9e17a6c8;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/RenewalCellScale.lean. Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/RenewalCellScale.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.OriginalGradientRenewal

/-! # A concrete power radius for original gradient renewal -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

noncomputable section

def renewalCellRadius (K : ℝ) (J q : ℕ) : ℝ := (K ^ (4 * J + q + 12))⁻¹

/-- A single explicit power radius absorbs all relative-Hessian errors.
Its exponent depends on J and the breadth exponent, before every source
entry and format datum. -/
theorem renewalCellRadius_absorbs
    {K A B δ : ℝ} {J q : ℕ} (hK : 2 ≤ K) (hA : 2 ≤ A) (hAK : A ≤ K)
    (hB : 0 ≤ B) (hBK : B ≤ K) (hδ : 0 < δ) (hδfloor : (K ^ q)⁻¹ ≤ δ) :
    0 < renewalCellRadius K J q ∧
      (3 * A ^ J) * (1 + (B + 2) / δ) *
        (3 * (8 : ℝ) ^ J * renewalCellRadius K J q * (1 + 2 * B)) ≤ 1 / 2 := by
  have hKp : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hAp : 0 ≤ A := by linarith
  have hInv : δ⁻¹ ≤ K ^ q := by
    simpa only [inv_inv] using inv_anti₀ (show 0 < (K ^ q)⁻¹ by positivity) hδfloor
  have hK2 : (4 : ℝ) ≤ K ^ 2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hK 2
    norm_num at hh
    exact hh
  have htwok : 2 * K ≤ K ^ 2 := by
    nlinarith [mul_nonneg hKp.le (sub_nonneg.mpr hK)]
  have hBplus : B + 2 ≤ K ^ 2 := (show B + 2 ≤ 2 * K by linarith).trans htwok
  have hC : 1 + (B + 2) / δ ≤ K ^ (q + 3) := by
    have hrough : (B + 2) / δ ≤ K ^ (q + 2) := by
      rw [div_eq_mul_inv]
      calc
        _ ≤ K ^ 2 * K ^ q := mul_le_mul hBplus hInv (by positivity) (by positivity)
        _ = _ := by rw [pow_add]; ring
    calc
      _ ≤ 1 + K ^ (q + 2) := add_le_add le_rfl hrough
      _ ≤ 2 * K ^ (q + 2) := by have := one_le_pow₀ hK1 (n := q + 2); linarith
      _ ≤ K * K ^ (q + 2) := mul_le_mul_of_nonneg_right hK (by positivity)
      _ = _ := by rw [show q + 3 = (q + 2) + 1 by omega, pow_succ]; ring
  have hBfactor : 1 + 2 * B ≤ K ^ 3 := by
    calc
      _ ≤ 3 * K := by linarith
      _ ≤ K ^ 2 * K := mul_le_mul_of_nonneg_right (show 3 ≤ K ^ 2 by linarith) hKp.le
      _ = _ := by ring
  have h9 : (9 : ℝ) ≤ K ^ 4 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hK 4
    norm_num at hh
    linarith
  have hAterm : A ^ J ≤ K ^ J := pow_le_pow_left₀ hAp hAK J
  have h8term : (8 : ℝ) ^ J ≤ K ^ (3 * J) := by
    have hh : (8 : ℝ) ≤ K ^ 3 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hK 3
      norm_num at hh
      exact hh
    exact (pow_le_pow_left₀ (by norm_num) hh J).trans_eq (by rw [← pow_mul])
  have hF : 9 * A ^ J * (8 : ℝ) ^ J * (1 + (B + 2) / δ) * (1 + 2 * B) ≤
      K ^ (4 * J + q + 10) := by
    calc
      _ ≤ K ^ 4 * K ^ J * K ^ (3 * J) * K ^ (q + 3) * K ^ 3 := by
        gcongr <;> assumption
      _ = _ := by simp only [← pow_add]; congr 1; omega
  have hid : K ^ (4 * J + q + 10) * renewalCellRadius K J q = (K ^ 2)⁻¹ := by
    dsimp only [renewalCellRadius]
    have hpow : K ^ (4 * J + q + 12) = K ^ (4 * J + q + 10) * K ^ 2 := by
      rw [← pow_add]
    rw [hpow]
    field_simp
  refine ⟨by dsimp only [renewalCellRadius]; positivity, ?_⟩
  calc
    _ = (9 * A ^ J * (8 : ℝ) ^ J * (1 + (B + 2) / δ) * (1 + 2 * B)) *
        renewalCellRadius K J q := by ring
    _ ≤ K ^ (4 * J + q + 10) * renewalCellRadius K J q :=
      mul_le_mul_of_nonneg_right hF (by dsimp only [renewalCellRadius]; positivity)
    _ = (K ^ 2)⁻¹ := hid
    _ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hK2
    _ ≤ 1 / 2 := by norm_num

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
