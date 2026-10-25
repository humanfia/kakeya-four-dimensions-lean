-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.PaletteCaps.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.EnergyWeights

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Reflection of palette indices is exact up to one factor of the base. -/
theorem palScale_reflection {r : ℝ} {n a i : ℕ} (hr : 0 < r) (hi : i ≤ a) :
    palScale r n a / palScale r n (i + 1) = palBase r n * palScale r n (a - i) := by
  have hB := palBase_pos (n := n) hr
  unfold palScale
  rw [← Real.rpow_sub hB]
  calc
    _ = palBase r n ^ ((1 : ℝ) + -((a - i : ℕ) : ℝ)) := by
      congr 1
      push_cast [Nat.cast_sub hi]
      ring
    _ = palBase r n ^ (1 : ℝ) * palBase r n ^ (-((a - i : ℕ) : ℝ)) :=
      Real.rpow_add hB _ _
    _ = _ := by rw [Real.rpow_one]

/-- The angular radius in the distance-shell estimate is no larger than
a fixed constant times the next reflected palette scale. -/
theorem reflected_cap_radius_le {r : ℝ} {n a i : ℕ}
    (hr : 0 < r) (hr1 : r < 1) (hn : 0 < n) (hi : i ≤ a) :
    Columns.paletteCapRadius (2 * palScale r n a) (fun j => 2 * palScale r n j) a i ≤
      300 * palBase r n * palScale r n (a - i) := by
  have hB := palBase_gt_one hr hr1 hn
  have hR := palScale_pos (n := n) hr a
  have hσ := palScale_pos (n := n) hr (a - i)
  unfold Columns.paletteCapRadius
  split_ifs with hia
  · subst i
    simp only [Nat.sub_self, palScale, Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one]
    linarith
  · have hρ := palScale_pos (n := n) hr (i + 1)
    calc
      _ ≤ 288 * (2 * palScale r n a) / (2 * palScale r n (i + 1)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (le_max_left _ _)
      _ = 288 * (palScale r n a / palScale r n (i + 1)) := by ring
      _ = 288 * (palBase r n * palScale r n (a - i)) := by rw [palScale_reflection hr hi]
      _ ≤ _ := by nlinarith

theorem reflected_cap_radius_pos {r : ℝ} {n a i : ℕ} (hr : 0 < r) :
    0 < Columns.paletteCapRadius (2 * palScale r n a) (fun j => 2 * palScale r n j) a i := by
  have hR := palScale_pos (n := n) hr a
  unfold Columns.paletteCapRadius
  split_ifs
  · norm_num
  · apply div_pos (by positivity)
    exact lt_of_lt_of_le (by positivity) (le_max_right _ _)

variable {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2} {D S J₀ : Finset (E2 × E2)}
  {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)}
  {tb : ℕ → E2 × E2 → E2 × E2}

/-- Every reflected cap count is bounded by the original fine bush mass
divided by its measured angular count at the reflected index. -/
theorem HighConfig.reflected_cap_count
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    (hr1 : r < 1) (hn : 0 < n) {a i : ℕ} (hia : i ≤ a) (han : a ≤ n)
    {p₀ : E2} (hp₀ : p₀ ∈ S.image Prod.fst) (p u : E2) :
    (((bushOf S p).filter (fun v => dist v u ≤
      Columns.paletteCapRadius (2 * palScale r n a) (fun j => 2 * palScale r n j) a i)).card : ℝ) ≤
      1000000 * (palBase r n) ^ (2 : ℕ) * r ^ (-ε) * (bushOf S p₀).card /
        cellCount (bushOf S p₀) (palScale r n (a - i)) := by
  have hr := H.fail.r_pos
  have hB := palBase_gt_one hr hr1 hn
  have hσ := palScale_pos (n := n) hr (a - i)
  have hθ := reflected_cap_radius_pos (n := n) (a := a) (i := i) hr
  have hθupper := reflected_cap_radius_le hr hr1 hn hia
  have hσn : a - i ≤ n := (Nat.sub_le a i).trans han
  have hh := Columns.bush_ball_global S hσ hθ (Real.rpow_nonneg hr.le (-ε))
    (H.bal_pin_arc (a - i) hσn) p₀ p u
  have hratio : 2 * Columns.paletteCapRadius (2 * palScale r n a)
      (fun j => 2 * palScale r n j) a i / palScale r n (a - i) ≤ 600 * palBase r n := by
    rw [div_le_iff₀ hσ]
    linarith
  have hratio0 : 0 ≤ 2 * Columns.paletteCapRadius (2 * palScale r n a)
      (fun j => 2 * palScale r n j) a i / palScale r n (a - i) := by positivity
  have hsquare : (2 * Columns.paletteCapRadius (2 * palScale r n a)
      (fun j => 2 * palScale r n j) a i / palScale r n (a - i) + 2) ^ 2 ≤
        1000000 * (palBase r n) ^ (2 : ℕ) := by
    calc
      _ ≤ (602 * palBase r n) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ ≤ _ := by nlinarith [sq_nonneg (palBase r n)]
  have hA : (0 : ℝ) < cellCount (bushOf S p₀) (palScale r n (a - i)) :=
    Nat.cast_pos.mpr (cellCount_pos (H.bush_nonempty hp₀) _)
  rw [le_div_iff₀ hA]
  have hmul := mul_le_mul_of_nonneg_left hsquare
    (show 0 ≤ r ^ (-ε) * (bushOf S p₀).card by positivity)
  convert hh.trans hmul using 1 <;> first | rfl | ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
