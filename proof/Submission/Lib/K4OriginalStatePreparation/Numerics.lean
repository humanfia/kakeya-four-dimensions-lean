/- Adapted from: here:o247 (session x0870, original proofs in commits
4fa3d421, 60e815aa, 71be63c4, and 30be2d73). -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Submission.Lib.K4OriginalStatePreparation

noncomputable section

/-- A ceiling of a weight ratio at least one costs at most a factor two. -/
theorem copy_count_bounds {β : ℝ} (hβ : 1 ≤ β) :
    0 < ⌈β⌉₊ ∧ β ≤ (⌈β⌉₊ : ℝ) ∧ (⌈β⌉₊ : ℝ) ≤ 2 * β := by
  have hlo : β ≤ (⌈β⌉₊ : ℝ) := Nat.le_ceil _
  have hhi : (⌈β⌉₊ : ℝ) < β + 1 := Nat.ceil_lt_add_one (by linarith)
  have hpos : (0 : ℝ) < (⌈β⌉₊ : ℝ) := by linarith
  exact ⟨by exact_mod_cast hpos, hlo, by linarith⟩

/-- The ratio of coarse and fine original projected weights is independent
of the original palette bin and the original base Jacobian. -/
theorem layer_weight_ratio {N : ℝ} (hN : 0 < N) (s t d W : ℝ) :
    N ^ (d * t) * (W * (N ^ (-s - t)) ^ d) = W * (N ^ (-s)) ^ d := by
  rw [show N ^ (d * t) * (W * (N ^ (-s - t)) ^ d) =
    W * (N ^ (d * t) * (N ^ (-s - t)) ^ d) by ring]
  rw [← Real.rpow_mul hN.le, ← Real.rpow_add hN, ← Real.rpow_mul hN.le]
  congr 1
  ring

/-- One common copy count equalizes all original velocity-bin weights at
these two depths, including bins of zero palette weight. -/
theorem layer_copy_count {N d t : ℝ} (hN : 1 ≤ N) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (s : ℝ) :
    ∃ r : ℕ, 0 < r ∧ ∀ W : ℝ, 0 ≤ W →
      W * (N ^ (-s)) ^ d ≤ (r : ℝ) * (W * (N ^ (-s - t)) ^ d) ∧
      (r : ℝ) * (W * (N ^ (-s - t)) ^ d) ≤ 2 * (W * (N ^ (-s)) ^ d) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hβ : 1 ≤ N ^ (d * t) := Real.one_le_rpow hN (mul_nonneg hd ht)
  obtain ⟨hr, hlo, hhi⟩ := copy_count_bounds hβ
  refine ⟨⌈N ^ (d * t)⌉₊, hr, ?_⟩
  intro W hW
  have hf : 0 ≤ W * (N ^ (-s - t)) ^ d := by positivity
  have heq := layer_weight_ratio hNp s t d W
  constructor
  · rw [← heq]
    exact mul_le_mul_of_nonneg_right hlo hf
  · calc
      _ ≤ (2 * N ^ (d * t)) * (W * (N ^ (-s - t)) ^ d) :=
        mul_le_mul_of_nonneg_right hhi hf
      _ = 2 * (W * (N ^ (-s)) ^ d) := by rw [mul_assoc, heq]

/-- The prescribed wide threshold leaves four full powers of the depth
increment in the neighboring-jet exponent. -/
theorem wide_dimension_margin {d u : ℝ} (hd : d < 1) (hu : 0 < u) :
    d * (10 / (1 - d) * u) + d * u + 4 * u <
      ((1 + d) / 2) * (10 / (1 - d) * u) := by
  have hden : 1 - d ≠ 0 := ne_of_gt (sub_pos.mpr hd)
  have heq : ((1 + d) / 2) * (10 / (1 - d) * u) -
      (d * (10 / (1 - d) * u) + d * u + 4 * u) = (1 - d) * u := by
    field_simp [hden]
    ring
  have hp := mul_pos (sub_pos.mpr hd) hu
  linarith

/-- A fine-layer factor and four subpower margins are absorbed by the
strictly subcritical exponent `(1+d)/2` at every larger discrepancy scale. -/
theorem wide_jet_power_bound {N d u R : ℝ} (hN : 1 ≤ N) (hd : d < 1)
    (hu : 0 < u) (hR : N ^ (10 / (1 - d) * u) ≤ R) :
    R ^ d * N ^ (d * u + 4 * u) ≤ R ^ ((1 + d) / 2) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hRp : 0 < R := (Real.rpow_pos_of_pos hNp _).trans_le hR
  have hgap : 0 ≤ (1 + d) / 2 - d := by linarith
  have hm : d * u + 4 * u ≤ (10 / (1 - d) * u) * ((1 + d) / 2 - d) := by
    have hh := wide_dimension_margin hd hu
    nlinarith
  have hpower : N ^ (d * u + 4 * u) ≤ R ^ ((1 + d) / 2 - d) := by
    calc
      _ ≤ N ^ ((10 / (1 - d) * u) * ((1 + d) / 2 - d)) :=
        Real.rpow_le_rpow_of_exponent_le hN hm
      _ = (N ^ (10 / (1 - d) * u)) ^ ((1 + d) / 2 - d) := Real.rpow_mul hNp.le _ _
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hNp.le _) hR hgap
  calc
    _ ≤ R ^ d * R ^ ((1 + d) / 2 - d) :=
      mul_le_mul_of_nonneg_left hpower (Real.rpow_nonneg hRp.le _)
    _ = R ^ (d + ((1 + d) / 2 - d)) := (Real.rpow_add hRp _ _).symm
    _ = _ := by congr 1; ring

end

end Submission.Lib.K4OriginalStatePreparation
