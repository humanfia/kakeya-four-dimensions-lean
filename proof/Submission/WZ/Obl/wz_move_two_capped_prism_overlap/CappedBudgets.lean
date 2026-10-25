-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.CappedBudgets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.NarrowStageTwo
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PowerBudgets

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, CappedBudgets.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open WangZahlLot.Obl.wz_clustered_cover_volume_gain (geometricPacketOverlap
  uniform_small_power_comparison)

structure CappedPowerBudgets (δ h ε ν β : ℝ) : Prop where
  cut : 16 * δ ^ ν ≤ δ ^ h
  narrow : 4 * δ ^ (2 * ν) ≤ δ ^ ν
  select : (((10 ^ 40 + 1 : ℕ) : ℝ) ^ 14) * δ ^ (3 * ν) ≤ δ ^ (2 * ν)
  merge : 8796093022208 * δ ^ (ε / 2 - ε / 100) ≤ δ ^ (3 * ν)
  angular : δ ^ (-(3 * ν)) * (16384 : ℝ) ^ β ≤ δ ^ (-(ε / 2))
  fair : (geometricPacketOverlap : ℝ) * δ ^ ε ≤ δ ^ (ε / 2)
  transverse : 46080 * δ ^ (12 * ν) < δ ^ (5 * ν)

/-- All fixed losses in capped disjointification fit one uniform cutoff. -/
theorem exists_capped_power_budgets {ε ν β : ℝ} (hε : 0 < ε) (hν : 0 < ν)
    (hνε : ν ≤ ε / 1000) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ h : ℝ, 0 < δ → δ ≤ 1 → δ ≤ d → h ≤ ν / 10 →
      CappedPowerBudgets δ h ε ν β := by
  let C : ℝ := (((10 ^ 40 + 1 : ℕ) : ℝ) ^ 14) +
    (geometricPacketOverlap : ℝ) + 8796093022208 + (16384 : ℝ) ^ β + 100000
  have hsel : 0 ≤ (((10 ^ 40 + 1 : ℕ) : ℝ) ^ 14) := by positivity
  have hfair : 0 ≤ (geometricPacketOverlap : ℝ) := Nat.cast_nonneg _
  have hang : 0 < (16384 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) _
  have hC : 0 < C := by dsimp [C]; linarith
  obtain ⟨d, hd, Hd⟩ := uniform_small_power_comparison hC (show 0 < ν / 4 by positivity)
  refine ⟨d, hd, ?_⟩
  intro δ h hδ hδ1 hδd hh
  have H := Hd δ hδ hδ1 hδd
  refine ⟨H 16 ν h ?_ ?_, H 4 (2 * ν) ν ?_ ?_,
    H _ (3 * ν) (2 * ν) ?_ ?_, H _ (ε / 2 - ε / 100) (3 * ν) ?_ ?_,
    ?_, H _ ε (ε / 2) ?_ ?_, ?_⟩
  all_goals try linarith
  all_goals try (dsimp [C]; linarith)
  · have hh := H ((16384 : ℝ) ^ β) (-(3 * ν)) (-(ε / 2))
      (by dsimp [C]; linarith) (by linarith)
    simpa only [mul_comm] using hh
  · have hh := H 92160 (12 * ν) (5 * ν) (by dsimp [C]; linarith) (by linarith)
    have hp := Real.rpow_pos_of_pos hδ (12 * ν)
    linarith

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
