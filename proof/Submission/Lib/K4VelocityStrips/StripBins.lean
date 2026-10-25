/-
Adapted from: here:o116

Original base-known midpoint-bin proof by session x0644.
-/

import Mathlib

/-! A strip's midpoint-position label is known from the current base observation
up to a short list, even though the trajectory velocity is not observed. -/

noncomputable section

namespace Submission.Lib.K4VelocityStrips

open scoped RealInnerProductSpace

def midpointBinList (r : ℝ) (n : EuclideanSpace ℝ (Fin 2)) (β t : ℝ)
    (Y : EuclideanSpace ℝ (Fin 2)) (C : ℕ) : Finset ℤ :=
  let q := ⌊(inner ℝ Y n + (1 / 2 - t) * β) / r⌋
  Finset.Icc (q - C) (q + C)

theorem midpointBinList_card (r : ℝ) (n : EuclideanSpace ℝ (Fin 2)) (β t : ℝ)
    (Y : EuclideanSpace ℝ (Fin 2)) (C : ℕ) :
    (midpointBinList r n β t Y C).card = 2 * C + 1 := by
  dsimp [midpointBinList]
  rw [Int.card_Icc]
  have hid (q : ℤ) : q + (C : ℤ) + 1 - (q - C) = (2 * C + 1 : ℕ) := by omega
  rw [hid, Int.toNat_natCast]

/-- A velocity-strip bound determines the midpoint bin to within `C` integer
steps from a function of the time and spatial base alone. -/
theorem midpoint_bin_mem_list {r β t : ℝ} {C : ℕ}
    {a v n : EuclideanSpace ℝ (Fin 2)} (hr : 0 < r)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hvel : |inner ℝ v n - β| ≤ (C : ℝ) * r) :
    ⌊inner ℝ (a + (1 / 2 : ℝ) • v) n / r⌋ ∈
      midpointBinList r n β t (a + t • v) C := by
  let actual : ℝ := inner ℝ (a + (1 / 2 : ℝ) • v) n
  let predicted : ℝ := inner ℝ (a + t • v) n + (1 / 2 - t) * β
  have hid : actual - predicted = (1 / 2 - t) * (inner ℝ v n - β) := by
    simp only [actual, predicted, inner_add_left, real_inner_smul_left]
    ring
  have htime : |(1 / 2 : ℝ) - t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have herror : |actual / r - predicted / r| ≤ (C : ℝ) := by
    rw [← sub_div, abs_div, abs_of_pos hr, div_le_iff₀ hr, hid, abs_mul]
    simpa only [one_mul] using
      (mul_le_mul htime hvel (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
  have hlo : predicted / r - (C : ℤ) ≤ actual / r := by
    have h := (abs_le.mp herror).1
    norm_cast
    linarith
  have hhi : actual / r ≤ predicted / r + (C : ℤ) := by
    have h := (abs_le.mp herror).2
    norm_cast
    linarith
  have hlo' := Int.floor_mono hlo
  have hhi' := Int.floor_mono hhi
  change ⌊actual / r⌋ ∈ Finset.Icc (⌊predicted / r⌋ - C) (⌊predicted / r⌋ + C)
  rw [Finset.mem_Icc]
  constructor
  · simpa using hlo'
  · simpa using hhi'

/-- The left endpoint of the midpoint floor bin is a valid whole-block center
parameter for the narrower frame. -/
theorem midpoint_floor_center_bound {r : ℝ} (hr : 0 < r) (z : ℝ) :
    |z - (⌊z / r⌋ : ℝ) * r| ≤ r := by
  have hlo := Int.floor_le (z / r)
  have hhi := Int.lt_floor_add_one (z / r)
  have hlo' := (le_div_iff₀ hr).mp hlo
  have hhi' := (div_lt_iff₀ hr).mp hhi
  rw [abs_of_nonneg (by linarith : 0 ≤ z - (⌊z / r⌋ : ℝ) * r)]
  nlinarith

end Submission.Lib.K4VelocityStrips
