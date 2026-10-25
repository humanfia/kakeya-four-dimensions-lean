-- Adapted from this LOT tree, o206, session x0709, commit f7d6ac58,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/DyadicMagnitude.lean.
-- Adapted from this LOT tree, o104, session x0472, commit 1aecc7d,
-- Submission/Obl/k4_terminal_time_extension/DyadicMagnitude.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_matching_homogeneous_records.Select

namespace Submission.Obl.k4_homogeneous_native_pair_preparation.Construction

open Set Filter

/-- A finite range of dyadic magnitudes covering the prescribed power range. -/
noncomputable def magnitudeGrid (N a : ℝ) : Finset ℤ :=
  Finset.Icc ⌊-a * Real.logb 2 N⌋ ⌊a * Real.logb 2 N⌋

/-- The dyadic bin containing a positive magnitude. -/
noncomputable def magnitudeIndex (x : ℝ) : ℤ := ⌊Real.logb 2 x⌋

theorem magnitudeIndex_bounds {x : ℝ} (hx : 0 < x) :
    (2 : ℝ) ^ magnitudeIndex x ≤ x ∧ x < 2 * (2 : ℝ) ^ magnitudeIndex x := by
  have hl := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hx).mp
    (Int.floor_le (Real.logb 2 x))
  have hu := (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) hx).mp
    (Int.lt_floor_add_one (Real.logb 2 x))
  rw [Real.rpow_intCast] at hl
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_intCast,
    Real.rpow_one] at hu
  exact ⟨hl, by simpa [magnitudeIndex, mul_comm] using hu⟩

/-- Distinct half-open dyadic magnitude bins do not overlap. -/
theorem dyadic_magnitude_unique {x : ℝ} {i j : ℤ}
    (hi : (2 : ℝ) ^ i ≤ x ∧ x < 2 * (2 : ℝ) ^ i)
    (hj : (2 : ℝ) ^ j ≤ x ∧ x < 2 * (2 : ℝ) ^ j) : i = j := by
  have hnot (i j : ℤ)
      (hi : (2 : ℝ) ^ i ≤ x ∧ x < 2 * (2 : ℝ) ^ i)
      (hj : (2 : ℝ) ^ j ≤ x ∧ x < 2 * (2 : ℝ) ^ j)
      (hij : i < j) : False := by
    have hh := zpow_right_mono₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show i + 1 ≤ j by omega)
    change (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ j at hh
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one] at hh
    exact hi.2.not_ge (by simpa only [mul_comm] using hh.trans hj.1)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact hnot i j hi hj hij
  · exact hnot j i hj hi hji

theorem magnitudeIndex_eq_iff {x : ℝ} (hx : 0 < x) (i : ℤ) :
    magnitudeIndex x = i ↔ (2 : ℝ) ^ i ≤ x ∧ x < 2 * (2 : ℝ) ^ i := by
  constructor
  · intro hi
    simpa only [hi] using magnitudeIndex_bounds hx
  · intro hi
    exact dyadic_magnitude_unique (magnitudeIndex_bounds hx) hi

theorem magnitudeIndex_mem {N a x : ℝ} (hN : 0 < N) (hx : 0 < x)
    (hlo : N ^ (-a) ≤ x) (hhi : x ≤ N ^ a) :
    magnitudeIndex x ∈ magnitudeGrid N a := by
  have hmon : MonotoneOn (Real.logb 2) (Ioi 0) :=
    (Real.strictMonoOn_logb (by norm_num : (1 : ℝ) < 2)).monotoneOn
  have hl := hmon (Real.rpow_pos_of_pos hN (-a)) hx hlo
  have hu := hmon hx (Real.rpow_pos_of_pos hN a) hhi
  rw [Real.logb_rpow_eq_mul_logb_of_pos hN] at hl hu
  exact Finset.mem_Icc.mpr ⟨Int.floor_mono hl, Int.floor_mono hu⟩

theorem magnitudeGrid_card_bound {N a : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a) :
    ((magnitudeGrid N a).card : ℝ) ≤ 2 * a * Real.logb 2 N + 2 := by
  have hL : 0 ≤ Real.logb 2 N := Real.logb_nonneg (by norm_num) hN
  have horder : ⌊-a * Real.logb 2 N⌋ ≤ ⌊a * Real.logb 2 N⌋ :=
    Int.floor_mono (by nlinarith)
  have hnonneg : (0 : ℤ) ≤ ⌊a * Real.logb 2 N⌋ + 1 - ⌊-a * Real.logb 2 N⌋ := by omega
  have hcast :
      (((⌊a * Real.logb 2 N⌋ + 1 - ⌊-a * Real.logb 2 N⌋).toNat : ℕ) : ℝ) =
      ((⌊a * Real.logb 2 N⌋ + 1 - ⌊-a * Real.logb 2 N⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnonneg
  rw [magnitudeGrid, Int.card_Icc, hcast]
  push_cast
  linarith [Int.floor_le (a * Real.logb 2 N), Int.lt_floor_add_one (-a * Real.logb 2 N)]

/-- The full admissible dyadic magnitude range has subpower size. -/
theorem magnitudeGrid_card_subpower (a : ℝ) (ha : 0 ≤ a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℝ in atTop, ((magnitudeGrid N a).card : ℝ) ≤ N ^ ε := by
  obtain ⟨N₀, hN₀⟩ := Submission.Obl.k4_matching_homogeneous_records.exists_log_pow_le
    (2 * a + 2) ε 1 (by positivity) hε
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop (1 : ℝ)] with N hN hN₁
  have hL : 0 ≤ Real.logb 2 N := Real.logb_nonneg (by norm_num) hN₁
  have hb := hN₀ N hN
  simp only [pow_one] at hb
  exact (magnitudeGrid_card_bound hN₁ ha).trans (le_trans (by nlinarith) hb)

end Submission.Obl.k4_homogeneous_native_pair_preparation.Construction
