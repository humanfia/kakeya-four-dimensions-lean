-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.ScalarExpansionNumerics.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
-- Ported from session x0272 (o103 repository, branch x0272, commit 05f6197); namespace renamed to `SP`.
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.ScalarSelfSum
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.PowerBudget

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

/-- The algebraic closure of small projections costs a fixed power of the
initial error, including the lower cutoff on the initial scalars. -/
theorem scalar_algebra_power_bound {δ κ K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hκ : 0 < κ) (hK : 0 ≤ K) (hKb : K ≤ δ ^ (-κ))
    (hconst : 52488 ≤ δ ^ (-κ)) :
    scalarAlgebraBound (δ ^ (100 * κ)) K ≤ δ ^ (-1000 * κ) := by
  let B := 144 * K ^ 2 / δ ^ (100 * κ)
  have h144 : (144 : ℝ) ≤ δ ^ (-κ) := (by norm_num : (144 : ℝ) ≤ 52488).trans hconst
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBb : B ≤ δ ^ (-103 * κ) := by
    calc
      B ≤ δ ^ (-κ) * (δ ^ (-κ)) ^ 2 / δ ^ (100 * κ) := by dsimp [B]; gcongr
      _ = δ ^ (-103 * κ) := by
        rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ, ← Real.rpow_sub hδ]
        congr 1
        norm_num
        ring
  have hD : 144 * B ^ 2 / δ ^ (100 * κ) ≤ δ ^ (-307 * κ) := by
    calc
      144 * B ^ 2 / δ ^ (100 * κ) ≤
          δ ^ (-κ) * (δ ^ (-103 * κ)) ^ 2 / δ ^ (100 * κ) := by gcongr
      _ = δ ^ (-307 * κ) := by
        rw [← Real.rpow_mul_natCast hδ.le, ← Real.rpow_add hδ, ← Real.rpow_sub hδ]
        congr 1
        norm_num
        ring
  have hB' : B ≤ δ ^ (-307 * κ) := hBb.trans
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  have hs : B + 144 * B ^ 2 / δ ^ (100 * κ) + 144 * B ^ 2 / δ ^ (100 * κ) ≤
      3 * δ ^ (-307 * κ) := by linarith
  calc
    scalarAlgebraBound (δ ^ (100 * κ)) K ≤ 9 * (6 * (3 * δ ^ (-307 * κ))) ^ 3 := by
      change 9 * (6 * (B + 144 * B ^ 2 / δ ^ (100 * κ) + 144 * B ^ 2 / δ ^ (100 * κ))) ^ 3 ≤ _
      gcongr
    _ = 52488 * δ ^ (-921 * κ) := by
      rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hδ.le]
      norm_num only [Nat.cast_ofNat]
      rw [show (-307 : ℝ) * κ * 3 = -921 * κ by ring]
      ring
    _ ≤ δ ^ (-κ) * δ ^ (-921 * κ) := mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = δ ^ (-922 * κ) := by rw [← Real.rpow_add hδ]; congr 1; ring
    _ ≤ δ ^ (-1000 * κ) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)

/-- A much coarser intermediate distance makes the near-collision budget
small enough for every exponent at least one half. -/
theorem scalar_expansion_collision_budget {δ κ σ C H : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 10000)
    (hσ : 1 / 2 ≤ σ) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hCb : C ≤ δ ^ (-κ)) (hHb : H ≤ δ ^ (-1000 * κ))
    (hconst : 52488 ≤ δ ^ (-κ)) :
    δ ≤ δ ^ (4000 * κ) ∧ δ ^ (4000 * κ) ≤ 1 ∧
      12 * H * C * (δ ^ (4000 * κ)) ^ σ ≤ 1 := by
  have h12 : (12 : ℝ) ≤ δ ^ (-κ) := (by norm_num : (12 : ℝ) ≤ 52488).trans hconst
  refine ⟨?_, Real.rpow_le_one hδ.le hδ1 (by positivity), ?_⟩
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : 4000 * κ ≤ 1)
  · calc
      12 * H * C * (δ ^ (4000 * κ)) ^ σ ≤
          δ ^ (-κ) * δ ^ (-1000 * κ) * δ ^ (-κ) * (δ ^ (4000 * κ)) ^ σ := by gcongr
      _ = δ ^ (4000 * κ * σ - 1002 * κ) := by
        rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
        congr 1
        ring
      _ ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by nlinarith)

theorem scalar_expansion_cover_upper {δ κ σ H N : ℝ}
    (hδ : 0 < δ) (hH : 0 ≤ H) (hN : 0 ≤ N)
    (hHb : H ≤ δ ^ (-1000 * κ)) (hNb : N ≤ δ ^ (-σ - κ))
    (hconst : 52488 ≤ δ ^ (-κ)) :
    (12 * H / δ ^ (4000 * κ)) * N ≤ δ ^ (-σ - 5002 * κ) := by
  have h12 : (12 : ℝ) ≤ δ ^ (-κ) := (by norm_num : (12 : ℝ) ≤ 52488).trans hconst
  calc
    (12 * H / δ ^ (4000 * κ)) * N ≤
        (δ ^ (-κ) * δ ^ (-1000 * κ) / δ ^ (4000 * κ)) * δ ^ (-σ - κ) := by gcongr
    _ = δ ^ (-σ - 5002 * κ) := by
      rw [← Real.rpow_add hδ, ← Real.rpow_sub hδ, ← Real.rpow_add hδ]
      congr 1
      ring

/-- A power cutoff near zero discards at most half of a Frostman set. -/
theorem scalar_cutoff_budget {δ κ σ C : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 10000) (hσ : 1 / 2 ≤ σ)
    (hC : C ≤ δ ^ (-κ)) (hconst : 52488 ≤ δ ^ (-κ)) :
    δ ≤ δ ^ (100 * κ) ∧ δ ^ (100 * κ) ≤ 1 ∧
      C * (δ ^ (100 * κ)) ^ σ ≤ 1 / 2 := by
  refine ⟨?_, Real.rpow_le_one hδ.le hδ1 (by positivity), ?_⟩
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : 100 * κ ≤ 1)
  · have hh := mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hδ.le κ)
    have hid : δ ^ (-κ) * δ ^ κ = 1 := by rw [← Real.rpow_add hδ]; simp
    rw [hid] at hh
    calc
      C * (δ ^ (100 * κ)) ^ σ ≤ δ ^ (-κ) * (δ ^ (100 * κ)) ^ σ := by gcongr
      _ = δ ^ (100 * κ * σ - κ) := by
        rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
        congr 1
        ring
      _ ≤ δ ^ κ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by nlinarith)
      _ ≤ 1 / 2 := by nlinarith [Real.rpow_pos_of_pos hδ κ]

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
