-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ProductNormalizationNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RingNumerics

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

theorem product_normalized_mesh_upper {δ κ t : ℝ} (hδ : 0 < δ) (ht : 0 < t)
    (hsize : δ ^ (100 * κ) ≤ t) :
    δ / t ^ 2 ≤ δ ^ (1 - 200 * κ) := by
  have hq := Real.rpow_pos_of_pos hδ (100 * κ)
  calc
    δ / t ^ 2 ≤ δ / (δ ^ (100 * κ)) ^ 2 := by gcongr
    _ = δ ^ (1 - 200 * κ) := by
      rw [pow_two, ← Real.rpow_add hδ, Real.rpow_sub hδ, Real.rpow_one]
      congr 2
      congr 1
      ring

theorem product_normalized_error {δ ρ κ η : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hρ : 0 < ρ) (hupper : ρ ≤ δ ^ (1 - 200 * κ))
    (hη : 0 < η) (hκ1 : κ ≤ 1 / 10000) (hκη : κ ≤ η / 100) :
    δ ^ (-κ) ≤ ρ ^ (-η) := by
  have he : κ ≤ (1 - 200 * κ) * η := by nlinarith
  calc
    δ ^ (-κ) ≤ δ ^ ((1 - 200 * κ) * (-η)) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith)
    _ = (δ ^ (1 - 200 * κ)) ^ (-η) := Real.rpow_mul hδ.le _ _
    _ ≤ ρ ^ (-η) := Real.rpow_le_rpow_of_nonpos hρ hupper (by linarith)

theorem product_normalized_gain {δ ρ κ σ g : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hρ : 0 < ρ) (hupper : ρ ≤ δ ^ (1 - 200 * κ))
    (hκ : 0 < κ) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hg : 0 < g) (hg1 : g ≤ 1) (hκg : κ ≤ g / 1000) :
    δ ^ (-σ - g / 2) ≤ ρ ^ (-σ - g) := by
  have hexp : (1 - 200 * κ) * (-σ - g) ≤ -σ - g / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hσ1 hκ.le
    have h2 := mul_le_mul_of_nonneg_left hg1 hκ.le
    nlinarith
  calc
    δ ^ (-σ - g / 2) ≤ δ ^ ((1 - 200 * κ) * (-σ - g)) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hexp
    _ = (δ ^ (1 - 200 * κ)) ^ (-σ - g) := Real.rpow_mul hδ.le _ _
    _ ≤ ρ ^ (-σ - g) := Real.rpow_le_rpow_of_nonpos hρ hupper (by linarith)

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
