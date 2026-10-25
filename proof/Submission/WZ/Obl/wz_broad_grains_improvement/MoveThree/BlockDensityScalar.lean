-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.BlockDensityScalar.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/BlockDensityScalar.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.SaturatedBodyEstimate

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set

/-- The normalized-prism density written as a gain over the short-scale
power, with the aspect ratio kept explicit. -/
theorem round_prism_density_identity {A K δ ρ a b m p σ ω ε : ℝ}
    (hA : 0 < A) (hK : 0 < K) (hδ : 0 < δ) (hρ : 0 < ρ)
    (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) (hp : 0 < p) :
    (4 * a * b) * (A / (110592 * K)) * (δ ^ (2 : ℕ)) ^ (ε / 2) *
        (Real.sqrt ((ρ ^ 2 / 64) / (4 * a * b)) / 16) ^ ω *
        m ^ (σ / 2) * p ^ (-σ) * ((ρ ^ 2 / 64) / (4 * a * b)) ^ (σ / 2) =
      (A / 110592 * (16 : ℝ) ^ (-σ) * (256 : ℝ) ^ (-ω)) / K * δ ^ ε *
        m ^ (σ / 2) * p ^ (-σ) * (ρ / a) ^ (σ + ω) *
        (a / b) ^ ((σ + ω) / 2) * (4 * a * b) := by
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have h64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have h256 : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]
    norm_num
  apply Real.log_injOn_pos (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow,
    Real.log_sqrt, Real.log_pow]
  rw [h4, h16, h64, h256]
  norm_num
  ring

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
