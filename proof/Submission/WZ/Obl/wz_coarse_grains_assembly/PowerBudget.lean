-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.PowerBudget.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.Defs
import Submission.WZ.Obl.wz_terminal_grains_restoration.Analysis

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

/-- A single negative-power budget absorbs a constant in every exponent
comparison that has at least the prescribed amount of slack. -/
theorem rpow_absorb {δ p a b C : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : C ≤ δ ^ (-p)) (hab : p + b ≤ a) : C * δ ^ a ≤ δ ^ b := by
  calc
    C * δ ^ a ≤ δ ^ (-p) * δ ^ a :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hδ.le _)
    _ = δ ^ (a - p) := by rw [← Real.rpow_add hδ]; congr 1; ring
    _ ≤ δ ^ b := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)

end WangZahlLot.Obl.wz_coarse_grains_assembly
