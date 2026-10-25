-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.RelativeNormalizationNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ProductNormalizationNumerics

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products


theorem relative_normalized_bounds {δ ρ κ g α : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hρ : 0 < ρ) (hupper : ρ ≤ δ ^ (1 - 200 * κ))
    (hκ : 0 < κ) (hg : 0 < g) (hg1 : g ≤ 1) (hκg : κ ≤ g / 10000)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    δ ^ (-(102 * κ)) ≤ ρ ^ (-g) ∧
    δ ^ (-α - κ) ≤ ρ ^ (-α - g) ∧
    δ ^ (-κ) ≤ ρ ^ (-g) * δ ^ (101 * κ) := by
  have hkg := mul_le_mul_of_nonneg_left hg1 hκ.le
  have hka := mul_le_mul_of_nonneg_left hα1 hκ.le
  have hfirst : δ ^ (-(102 * κ)) ≤ ρ ^ (-g) := by
    calc
      _ ≤ δ ^ ((1 - 200 * κ) * (-g)) :=
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith)
      _ = (δ ^ (1 - 200 * κ)) ^ (-g) := Real.rpow_mul hδ.le _ _
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos hρ hupper (by linarith)
  refine ⟨hfirst, ?_, ?_⟩
  · calc
      _ ≤ δ ^ ((1 - 200 * κ) * (-α - g)) :=
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith)
      _ = (δ ^ (1 - 200 * κ)) ^ (-α - g) := Real.rpow_mul hδ.le _ _
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos hρ hupper (by linarith)
  · calc
      δ ^ (-κ) = δ ^ (-(102 * κ)) * δ ^ (101 * κ) := by
        rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfirst (Real.rpow_nonneg hδ.le _)

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
