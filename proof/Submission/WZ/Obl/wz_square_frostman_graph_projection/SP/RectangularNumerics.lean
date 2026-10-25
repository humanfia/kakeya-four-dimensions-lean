-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.RectangularNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RectangularScalarTransfer

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

/-- A nonempty normalized Frostman set has the expected cardinality lower bound. -/
theorem RealFiniteFrostman.card_power_lower {δ κ C σ : ℝ} {B : Finset ℝ}
    (hBF : RealFiniteFrostman δ C σ B) (hδ : 0 < δ) (hB : B.Nonempty)
    (hC : C ≤ δ ^ (-κ)) : δ ^ (κ - σ) ≤ (B.card : ℝ) := by
  classical
  obtain ⟨b, hb⟩ := hB
  have hpoint : b ∈ B.filter (fun x => dist x b ≤ δ) := Finset.mem_filter.mpr ⟨hb, by simpa using hδ.le⟩
  have hc : (1 : ℝ) ≤ (B.filter (fun x => dist x b ≤ δ)).card := by
    exact_mod_cast Finset.one_le_card.mpr ⟨b, hpoint⟩
  have hh := hc.trans (hBF b δ le_rfl)
  apply grid_power_lower hδ (Nat.cast_nonneg _) hC
  nlinarith

theorem rectangular_card_ratio {δ κ σ N M : ℝ} (hδ : 0 < δ)
    (hN : N ≤ δ ^ (-σ - κ)) (hM : δ ^ (κ - σ) ≤ M) : N ≤ δ ^ (-2 * κ) * M := by
  calc
    N ≤ δ ^ (-σ - κ) := hN
    _ = δ ^ (-2 * κ) * δ ^ (κ - σ) := by rw [← Real.rpow_add hδ]; congr 1; ring
    _ ≤ δ ^ (-2 * κ) * M := mul_le_mul_of_nonneg_left hM (by positivity)

theorem rectangular_scalar_power_budget {δ κ a N M : ℝ} (hδ : 0 < δ)
    (ha : δ ^ (100 * κ) ≤ a) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hNM : N ≤ δ ^ (-2 * κ) * M) (hconst : 108 ≤ δ ^ (-κ)) :
    (108 * (δ ^ (-κ)) ^ 2 / a) * N ≤ δ ^ (-105 * κ) * M := by
  have hap : 0 < a := (Real.rpow_pos_of_pos hδ _).trans_le ha
  calc
    (108 * (δ ^ (-κ)) ^ 2 / a) * N ≤
        (δ ^ (-κ) * (δ ^ (-κ)) ^ 2 / δ ^ (100 * κ)) * (δ ^ (-2 * κ) * M) := by gcongr
    _ = δ ^ (-105 * κ) * M := by
      rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ, ← Real.rpow_sub hδ,
        ← mul_assoc, ← Real.rpow_add hδ]
      congr 1
      congr 1
      norm_num
      ring

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
