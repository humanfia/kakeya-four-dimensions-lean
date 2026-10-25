-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_normalized_prism_transfer.RegularBudgets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_normalized_prism_transfer.Defs
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PowerBudgets

namespace WangZahlLot.Obl.wz_move_two_normalized_prism_transfer

/-- A fixed number of size classes absorbs assignment and cover-balancing losses. -/
theorem regular_prism_budgets {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ (b : ℕ) (d₀ : ℝ), 0 < b ∧ 0 < d₀ ∧ d₀ < 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
        (10 ^ 16 : ℝ) * δ ^ (2 * s) ≤ δ ^ s ∧
        (1000000000000 : ℝ) ≤ δ ^ (-3 : ℝ) ∧
        1 < δ ^ (-s) ∧ δ ^ (-7 : ℝ) < (δ ^ (-s)) ^ b ∧
        (b : ℝ) * δ ^ (4 * s) ≤ δ ^ (2 * s) ∧
        δ ^ (-s) * (56 * δ ^ (-(4 * (4 * s)))) * δ ^ (-s) ≤ δ ^ (-(100 * s)) ∧
        δ ^ (-s) ≤ δ ^ (-(100 * s)) ∧ 1 ≤ δ ^ (-(100 * s)) := by
  let b : ℕ := ⌈8 / s⌉₊ + 1
  have hb : 0 < b := Nat.succ_pos _
  have hbs : 8 ≤ s * (b : ℝ) := by
    have hceil : 8 / s ≤ (b : ℝ) := by
      apply (Nat.le_ceil (8 / s)).trans
      exact_mod_cast Nat.le_succ ⌈8 / s⌉₊
    have hh := (div_le_iff₀ hs).mp hceil
    nlinarith
  let B : ℝ := 10 ^ 16 + b
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨d, hd, hcmp⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.uniform_small_power_comparison hB hs
  refine ⟨b, min d (1 / 2), hb, lt_min hd (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro δ hδ hδ0
  have hδlt : δ < 1 := lt_of_le_of_lt (hδ0.trans (min_le_right _ _)) (by norm_num)
  have hcmp' := hcmp δ hδ hδlt.le (hδ0.trans (min_le_left _ _))
  have hBlarge : (10 ^ 16 : ℝ) ≤ B := by
    dsimp [B]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hR : 1 < δ ^ (-s) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hδ hδlt (by linarith)
  refine ⟨hcmp' _ _ _ hBlarge (by linarith), ?_, hR, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Real.rpow_zero, mul_one] using
      hcmp' (1000000000000 : ℝ) 0 (-3) (by linarith) (by linarith)
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    exact Real.rpow_lt_rpow_of_exponent_gt hδ hδlt (by nlinarith)
  · exact hcmp' _ _ _ (by dsimp [B]; linarith) (by linarith)
  · calc
      _ = 56 * δ ^ (-18 * s) := by
        rw [mul_comm (δ ^ (-s)) (56 * δ ^ (-(4 * (4 * s)))),
          mul_assoc, ← Real.rpow_add hδ, mul_assoc, ← Real.rpow_add hδ]
        congr 2
        ring
      _ ≤ δ ^ (-(100 * s)) := hcmp' _ _ _ (by linarith) (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_ge hδ hδlt.le (by linarith)
  · simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hδ hδlt.le (show -(100 * s) ≤ 0 by linarith)

end WangZahlLot.Obl.wz_move_two_normalized_prism_transfer
