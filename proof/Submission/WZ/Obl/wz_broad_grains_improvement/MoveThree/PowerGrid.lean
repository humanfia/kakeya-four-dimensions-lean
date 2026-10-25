-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PowerGrid.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PowerGrid.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

/-- A finite sequence of consecutive powers covers its full scale range. -/
theorem finite_power_grid_cover {q r : ℝ} (N : ℕ) (hN : 0 < N)
    (hlow : q ^ N ≤ r) (hupp : r ≤ 1) :
    ∃ j : Fin N, q ^ (j.val + 1) ≤ r ∧ r ≤ q ^ j.val := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hzero : N = 0
    · subst N
      exact ⟨0, by simpa using hlow, by simpa using hupp⟩
    by_cases hlast : r ≤ q ^ N
    · exact ⟨⟨N, Nat.lt_succ_self N⟩, hlow, hlast⟩
    · obtain ⟨j, hjlow, hjupp⟩ := ih (Nat.pos_of_ne_zero hzero) (le_of_not_ge hlast)
      exact ⟨⟨j, j.isLt.trans (Nat.lt_succ_self N)⟩, hjlow, hjupp⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
