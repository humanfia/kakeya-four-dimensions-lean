import Submission.Obl.k4_scalar_conditional_crop_worlds.MarkedConstruction
import Submission.Obl.k4_scalar_conditional_crop_worlds.CropPriorFormat
import Submission.Obl.k4_scalar_conditional_crop_worlds.Numerics

open MeasureTheory

namespace Submission.Obl.k4_scalar_conditional_crop_worlds

noncomputable section

/-- Uniform polynomial format for the finite density boxes of marked scalar crops. -/
theorem priorInterface_marked (m u : ℝ) (hm : 0 < m) (hu : 0 ≤ u) (M B A : ℕ) :
    PriorInterface m u M B A := by
  let L := ⌈5 * m⌉₊ + A + 1
  let C := max M (max (B + 7) L)
  have hMC : M ≤ C := le_max_left _ _
  have hBC : B + 7 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hLC : L ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, 1, by omega, le_rfl, ?_⟩
  intro N K H b₀ w q p hN hK hB hH hw hw1 hb heq hp
  have hNp : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hσ : 0 < N ^ (-m) := Real.rpow_pos_of_pos hNp _
  have hσ1 : N ^ (-m) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have ha1 : N ^ (-u) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hp0 : 0 < p := (Real.rpow_pos_of_pos hNp _).trans_le hp
  have hR : 70 * (K + 1) ≤ N ^ C := by
    have h70 : (70 : ℝ) ≤ N ^ 7 := by
      have : (2 : ℝ) ^ 7 ≤ N ^ 7 := pow_le_pow_left₀ (by norm_num) hN 7
      norm_num at this ⊢
      linarith
    calc 70 * (K + 1) ≤ N ^ 7 * N ^ B :=
        mul_le_mul h70 hB (by linarith) (by positivity)
      _ = N ^ (B + 7) := by rw [← pow_add]; congr 1; omega
      _ ≤ N ^ C := pow_le_pow_right₀ hN1 hBC
  have hHR : (H : ℝ) ≤ N ^ C := by
    have hH' : (H : ℝ) ≤ N ^ M := by simpa only [Real.rpow_natCast] using hH
    exact hH'.trans (pow_le_pow_right₀ hN1 hMC)
  have hdensity : (N ^ (-m))⁻¹ ^ 5 / p ≤ N ^ L := by
    simpa only [L, neg_zero, Real.rpow_zero, one_pow, mul_one, one_mul] using
      crop_density_le (m := m) (u := 0) (w := 1) hN le_rfl A (by norm_num) le_rfl hp
  have hpR : (N ^ (-m))⁻¹ ^ 5 ≤ p * N ^ C := by
    have h := (div_le_iff₀ hp0).1 (hdensity.trans (pow_le_pow_right₀ hN1 hLC))
    simpa only [mul_comm] using h
  let ν₀ := MarkedPrior (N ^ (-m)) H b₀ w
  have hcell : ν₀ (scalarCell N u q) ≠ 0 := by
    intro hzero
    have h := hp0
    rw [heq] at h
    change 0 < (ν₀ (scalarCell N u q)).toReal at h
    rw [hzero, ENNReal.toReal_zero] at h
    exact lt_irrefl 0 h
  obtain ⟨hz0, hz1⟩ := cell_center_coordinate_bound hNp ν₀
    (markedPrior_ae_bound hσ b₀ w hb) q hcell
  exact conditionalPrior_priorData hNp ha1 hσ hσ1 b₀ w hw hw1 hb q
    (hz0.trans (by linarith)) (hz1.trans (by linarith)) hp0 hR hHR hpR

end

end Submission.Obl.k4_scalar_conditional_crop_worlds
