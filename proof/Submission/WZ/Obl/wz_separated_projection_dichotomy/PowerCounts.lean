-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.PowerCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Counting

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

theorem factor_threshold_eq {δ η : ℝ} (hδ : 0 < δ) :
    δ ^ (η - 3) / (δ ^ (-η) * (3 / δ)) ^ 2 = δ ^ (3 * η - 1) / 9 := by
  have hp := Real.rpow_pos_of_pos hδ η
  have h3 : δ ^ (3 * η - 1) = (δ ^ η) ^ 3 / δ := by
    rw [Real.rpow_sub hδ, show 3 * η = η * 3 by ring, Real.rpow_mul hδ.le]
    norm_num
  rw [h3, Real.rpow_sub hδ, Real.rpow_neg hδ.le]
  norm_num
  field_simp
  ring

theorem frostman_constant_eq {δ η : ℝ} (hδ : 0 < δ) :
    25 * δ ^ (-η) / (δ * (δ ^ (3 * η - 1) / 9)) = 225 * δ ^ (-4 * η) := by
  have hp := Real.rpow_pos_of_pos hδ η
  have h3 : δ ^ (3 * η - 1) = (δ ^ η) ^ 3 / δ := by
    rw [Real.rpow_sub hδ, show 3 * η = η * 3 by ring, Real.rpow_mul hδ.le]
    norm_num
  have h4 : δ ^ (-4 * η) = ((δ ^ η) ^ 4)⁻¹ := by
    rw [show -4 * η = -(η * 4) by ring, Real.rpow_neg hδ.le, Real.rpow_mul hδ.le]
    norm_num
  rw [h3, h4, Real.rpow_neg hδ.le]
  field_simp
  ring

theorem factor_coverLower_rpow {δ η : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {F G : Set Plane} (hF : InUnitSquare F) (hG : InUnitSquare G)
    (hAF : AD δ (δ ^ (-η)) F) (hAG : AD δ (δ ^ (-η)) G)
    {Q : Set Triple} (hQ : Q ⊆ F ×ˢ (G ×ˢ G))
    (hN : CoverLower δ Q (δ ^ (η - 3))) :
    CoverLower δ F (δ ^ (3 * η - 1) / 9) ∧
    CoverLower δ G (δ ^ (3 * η - 1) / 9) := by
  simpa only [factor_threshold_eq hδ] using
    factor_coverLower_of_AD hδ hδ1 hF hG hAF hAG hQ hN

end WangZahlLot.Obl.wz_separated_projection_dichotomy
