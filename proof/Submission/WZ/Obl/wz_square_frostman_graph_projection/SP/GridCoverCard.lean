-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.GridCoverCard.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.GridQuantization

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators

/-- Each real cover ball meets at most a fixed number of occupied grid cells. -/
theorem grid_image_card_le_cover {δ : ℝ} (hδ : 0 < δ) (A : Finset ℝ)
    {m : ℕ} (cc : Fin m → ℝ) (hcov : Covers δ (↑A : Set ℝ) cc) :
    ((A.image (realGridIndex δ)).card : ℝ) ≤ 6 * (m : ℝ) := by
  classical
  let D (i : Fin m) := Finset.Icc (realGridIndex δ (cc i) - 2) (realGridIndex δ (cc i) + 3)
  let S := Finset.univ.biUnion D
  have hcard (i : Fin m) : (D i).card = 6 := by
    simp only [D, Int.card_Icc]
    omega
  have hS : S.card ≤ 6 * m := by
    have hh := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin m))) (t := D)
    simpa only [hcard, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Nat.mul_comm] using hh
  have hsub : A.image (realGridIndex δ) ⊆ S := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov ha)
    have hea := realGridIndex_error hδ a
    have hec := realGridIndex_error hδ (cc i)
    have hdist := abs_le.mp (show |a - cc i| ≤ δ by simpa only [Metric.mem_closedBall, Real.dist_eq] using hi)
    have hlo : (realGridIndex δ (cc i) : ℝ) - 2 ≤ (realGridIndex δ a : ℝ) := by nlinarith
    have hhi : (realGridIndex δ a : ℝ) ≤ (realGridIndex δ (cc i) : ℝ) + 3 := by nlinarith
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
    · exact_mod_cast hlo
    · exact_mod_cast hhi
  exact_mod_cast (Finset.card_le_card hsub).trans hS

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
