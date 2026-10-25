-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.WeakScalarCutoff.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from x0563 on o141, commit b3b5488; owned namespace renamed.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ScalarExpansionNumerics

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products


/-- An arbitrarily small positive Frostman exponent still permits a power
cutoff when the input error is chosen sufficiently small. -/
theorem weak_scalar_cutoff_budget {δ κ η τ C : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 10000) (hbudget : 2 * η ≤ 100 * κ * τ)
    (hC : C ≤ δ ^ (-η)) (hconst : 2 ≤ δ ^ (-η)) :
    δ ≤ δ ^ (100 * κ) ∧ δ ^ (100 * κ) ≤ 1 ∧
      C * (δ ^ (100 * κ)) ^ τ ≤ 1 / 2 := by
  refine ⟨?_, Real.rpow_le_one hδ.le hδ1 (by positivity), ?_⟩
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : 100 * κ ≤ 1)
  · have hh := mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hδ.le η)
    have hid : δ ^ (-η) * δ ^ η = 1 := by rw [← Real.rpow_add hδ]; simp
    rw [hid] at hh
    calc
      C * (δ ^ (100 * κ)) ^ τ ≤ δ ^ (-η) * (δ ^ (100 * κ)) ^ τ := by gcongr
      _ = δ ^ (100 * κ * τ - η) := by
        rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
        congr 1
        ring
      _ ≤ δ ^ η := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ ≤ 1 / 2 := by linarith

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
