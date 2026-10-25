import Submission.Obl.k4_finite_affine_parent_sources.SourceSampleParameters
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionCapNumerics

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

/-- The sixth budget power pays both the original pure caps and the
intermediate stable-graph group cost, including its inverse-power floor. -/
theorem sample_pure_group_budget {Nk κ b hd τd δ₀ L A : ℝ}
    (hNk : 1 ≤ Nk) (hκ : 1 ≤ κ) (hb : 0 ≤ b) (hhd : hd ≤ b)
    (hτ : τd ≤ b) (hδ : 2 * (δ₀ * L) ≤ b)
    (hA : 10000 ≤ A) (hκA : 7 * κ ≤ A) (hpoly : 192 * (7 * κ) ^ 3 ≤ A)
    (hAeq : A = Nk ^ b) :
    pureConst κ Nk hd τd δ₀ L ≤ A ^ 4 ∧
      κ * (4 * Nk ^ hd + 2) * Nk ^ (τd + 2 * (δ₀ * L)) *
        (16 * (1 + (7 * κ) ^ 2)) ≤ A ^ 6 * A⁻¹ ∧
      2 ≤ A ^ 6 ∧ 7 * κ ≤ A ^ 6 := by
  have hNk0 : 0 < Nk := zero_lt_one.trans_le hNk
  have hκ0 : 0 ≤ κ := zero_le_one.trans hκ
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hnorm : Nk ^ (4 * b) = A ^ 4 := by
    rw [hAeq, ← Real.rpow_mul_natCast hNk0.le]
    congr 1
    norm_num
    ring
  have hpolyκ : 192 * κ ^ 3 ≤ Nk ^ b := by
    rw [← hAeq]
    calc 192 * κ ^ 3 ≤ 192 * (7 * κ) ^ 3 := by gcongr; linarith
      _ ≤ _ := hpoly
  have hsum : τd + 2 * (δ₀ * L) ≤ 2 * b := by linarith
  have hCp := pureConst_le_rpow (τd := τd) (δ₀ := δ₀) (L := L) hNk hκ hb hhd hsum hpolyκ
  rw [hnorm] at hCp
  have hCp7 := pureConst_le_rpow (τd := τd) (δ₀ := δ₀) (L := L)
    hNk (by linarith : 1 ≤ 7 * κ) hb hhd hsum (by rw [← hAeq]; exact hpoly)
  rw [hnorm] at hCp7
  refine ⟨hCp, ?_, ?_, ?_⟩
  · have hgroup : κ * (4 * Nk ^ hd + 2) * Nk ^ (τd + 2 * (δ₀ * L)) *
        (16 * (1 + (7 * κ) ^ 2)) ≤ pureConst (7 * κ) Nk hd τd δ₀ L := by
      unfold pureConst
      gcongr
      linarith
    have heq : A ^ 6 * A⁻¹ = A ^ 5 := by
      rw [pow_succ, mul_assoc, mul_inv_cancel₀ hA0.ne', mul_one]
    rw [heq]
    exact hgroup.trans (hCp7.trans (pow_le_pow_right₀ hA1 (by norm_num)))
  · exact (by linarith : 2 ≤ A).trans (le_self_pow₀ hA1 (by norm_num))
  · exact hκA.trans (le_self_pow₀ hA1 (by norm_num))

end

end Submission.Obl.k4_finite_affine_parent_sources
