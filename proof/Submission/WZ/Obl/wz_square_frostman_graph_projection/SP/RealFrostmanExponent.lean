-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.RealFrostmanExponent.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.CartesianFrostman

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products


/-- Lowering a nonnegative Frostman exponent preserves the bound, including
radii larger than one. -/
theorem RealFiniteFrostman.lower_exponent {δ C σ τ : ℝ} {A : Finset ℝ}
    (hF : RealFiniteFrostman δ C τ A) (hδ : 0 < δ) (hC : 1 ≤ C)
    (hσ : 0 ≤ σ) (hστ : σ ≤ τ) : RealFiniteFrostman δ C σ A := by
  intro x r hr
  have hrp : 0 < r := hδ.trans_le hr
  by_cases hr1 : r ≤ 1
  · exact (hF x r hr).trans (by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hrp hr1 hστ) (by linarith))
  · have hpow : 1 ≤ r ^ σ := Real.one_le_rpow (le_of_not_ge hr1) hσ
    have hc : 1 ≤ C * r ^ σ := by nlinarith
    have hn : ((A.filter (fun a => dist a x ≤ r)).card : ℝ) ≤ (A.card : ℝ) := by
      exact_mod_cast Finset.card_filter_le A _
    exact hn.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card))

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
