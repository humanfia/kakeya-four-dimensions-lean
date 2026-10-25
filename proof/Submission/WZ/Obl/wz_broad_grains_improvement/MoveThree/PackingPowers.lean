-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.PackingPowers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/PackingPowers.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ConcentratedPacking

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open WangZahlLot.Obl.wz_separated_cover_refinement (exists_rpow_cutoff)

noncomputable section

theorem grainPackingCoefficient_ge_one (δ ε : ℝ) : 1 ≤ grainPackingCoefficient δ ε := by
  have hK : (1 : ℝ) ≤ grainPackingColors δ ε := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hh := Real.sqrt_le_sqrt hK
  rw [Real.sqrt_one] at hh
  dsimp [grainPackingCoefficient]
  nlinarith only [hh]

/-- The absolute geometric constants and ceiling in the packing estimate
cost at most one additional small power of the fine scale. -/
theorem grainPackingCoefficient_power_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → grainPackingCoefficient δ ε ≤ δ ^ (-ε) := by
  let C₀ := grainOverlapConstant (1 / 20000)
  have hC₀ : 0 < C₀ := grainOverlapConstant_pos (by norm_num)
  let C := (10000000 : ℝ) ^ 2 * (C₀ + 2)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨d₀, hd₀, Hcut⟩ := exists_rpow_cutoff hε (inv_pos.mpr hC)
  refine ⟨min d₀ 1, lt_min hd₀ zero_lt_one, min_le_right _ _, ?_⟩
  intro δ hδ hδd
  have hδ1 : δ ≤ 1 := hδd.trans (min_le_right _ _)
  have hcpow : C ≤ δ ^ (-ε) := by
    have hh := inv_anti₀ (Real.rpow_pos_of_pos hδ ε) (Hcut δ hδ (hδd.trans (min_le_left _ _)))
    rwa [inv_inv, ← Real.rpow_neg hδ.le] at hh
  have hpow1 : 1 ≤ δ ^ (-(21 * ε / 40)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hceil := Nat.ceil_lt_add_one
    (mul_nonneg hC₀.le (Real.rpow_nonneg hδ.le (-(21 * ε / 40))))
  have hK : (grainPackingColors δ ε : ℝ) ≤ (C₀ + 2) * δ ^ (-(21 * ε / 40)) := by
    change ((⌈C₀ * δ ^ (-(21 * ε / 40))⌉₊ + 1 : ℕ) : ℝ) ≤ _
    push_cast
    nlinarith only [hceil, hpow1]
  have hsq : (grainPackingCoefficient δ ε) ^ 2 ≤ C * δ ^ (-(21 * ε / 40)) := by
    rw [grainPackingCoefficient, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    have hh := mul_le_mul_of_nonneg_left hK (sq_nonneg (10000000 : ℝ))
    simpa only [C, mul_assoc] using hh
  have hbound : C * δ ^ (-(21 * ε / 40)) ≤ (δ ^ (-ε)) ^ 2 := by
    calc
      _ ≤ δ ^ (-ε) * δ ^ (-(21 * ε / 40)) :=
        mul_le_mul_of_nonneg_right hcpow (Real.rpow_nonneg hδ.le _)
      _ = δ ^ (-(61 * ε / 40)) := by rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ δ ^ (-(2 * ε)) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      _ = _ := by rw [← Real.rpow_mul_natCast hδ.le]; congr 1; norm_num; ring
  exact (sq_le_sq₀ (by dsimp [grainPackingCoefficient]; positivity)
    (Real.rpow_nonneg hδ.le _)).mp (hsq.trans hbound)

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
