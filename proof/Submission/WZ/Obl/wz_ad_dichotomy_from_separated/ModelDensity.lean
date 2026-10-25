-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_ad_dichotomy_from_separated.ModelDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_ad_dichotomy_from_separated.Quantization

namespace WangZahlLot.Obl.wz_ad_dichotomy_from_separated

theorem model_density_scale_identity {δ η : ℝ} (hδ : 0 < δ) :
    (δ ^ (4 * η) / (75 : ℝ) ^ 3) * (75 * δ ^ (-η) / δ) ^ 3 = δ ^ (η - 3) := by
  have hp := Real.rpow_pos_of_pos hδ η
  have h4 : δ ^ (4 * η) = (δ ^ η) ^ 4 := by
    rw [show 4 * η = η * 4 by ring, Real.rpow_mul hδ.le]
    norm_num
  rw [h4, Real.rpow_neg hδ.le, Real.rpow_sub hδ]
  norm_num
  field_simp
  ring

/-- The upper cardinalities supplied by AD turn the absolute occupied-cell
threshold into a relative hypergraph density. These upper bounds are essential. -/
theorem model_relative_density {δ η : ℝ} (hδ : 0 < δ) (S T : Finset Plane)
    (H : Finset (S × T × T))
    (hS : (S.card : ℝ) ≤ 75 * δ ^ (-η) / δ)
    (hT : (T.card : ℝ) ≤ 75 * δ ^ (-η) / δ)
    (hH : δ ^ (η - 3) ≤ (H.card : ℝ)) :
    (δ ^ (4 * η) / (75 : ℝ) ^ 3) * (S.card : ℝ) * (T.card : ℝ) ^ 2 ≤
      (H.card : ℝ) := by
  calc (δ ^ (4 * η) / (75 : ℝ) ^ 3) * (S.card : ℝ) * (T.card : ℝ) ^ 2 ≤
        (δ ^ (4 * η) / (75 : ℝ) ^ 3) * (75 * δ ^ (-η) / δ) *
          (75 * δ ^ (-η) / δ) ^ 2 := by gcongr
    _ = (δ ^ (4 * η) / (75 : ℝ) ^ 3) * (75 * δ ^ (-η) / δ) ^ 3 := by ring
    _ = δ ^ (η - 3) := model_density_scale_identity hδ
    _ ≤ (H.card : ℝ) := hH

end WangZahlLot.Obl.wz_ad_dichotomy_from_separated
