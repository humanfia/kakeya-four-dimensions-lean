-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData.Rounding.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o214/x0665 WangZahlLot/Obl/wz_furstenberg_katz_tao_high/GraphData/Rounding.lean (82de8bd).
-- Copied from workspace o222, branch x0658 (commit 1206391), Rounding.lean; namespace renamed.
import Mathlib

/-!
# Rounding to a `δ`-grid

Elementary facts about `rd δ x = ⌊x / δ⌋ * δ`, used to make the coordinate
projections of a graph `δ`-separated.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

/-- Rounding down to the grid `δ ℤ`. -/
noncomputable def rd (δ x : ℝ) : ℝ := (⌊x / δ⌋ : ℝ) * δ

/-- Coordinatewise rounding of a point of the plane `ℝ × ℝ`. -/
noncomputable def rd2 (δ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (rd δ p.1, rd δ p.2)

lemma rd_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : rd δ x ≤ x := by
  have h := Int.floor_le (x / δ)
  have := mul_le_mul_of_nonneg_right h hδ.le
  rwa [div_mul_cancel₀ x hδ.ne'] at this

lemma lt_rd_add {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : x < rd δ x + δ := by
  have h := Int.lt_floor_add_one (x / δ)
  have := mul_lt_mul_of_pos_right h hδ
  rw [div_mul_cancel₀ x hδ.ne', add_mul, one_mul] at this
  exact this

lemma abs_sub_rd_lt {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : |x - rd δ x| < δ := by
  have h1 := rd_le hδ x
  have h2 := lt_rd_add hδ x
  rw [abs_lt]
  constructor <;> linarith

lemma abs_rd_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : |rd δ x| ≤ |x| + δ := by
  have h := abs_sub_rd_lt hδ x
  have : |rd δ x| ≤ |x| + |x - rd δ x| := by
    calc |rd δ x| = |x - (x - rd δ x)| := by ring_nf
      _ ≤ |x| + |x - rd δ x| := abs_sub _ _
  linarith

lemma rd_sep {δ : ℝ} (hδ : 0 < δ) {x y : ℝ} (h : rd δ x ≠ rd δ y) :
    δ ≤ dist (rd δ x) (rd δ y) := by
  have hne : ⌊x / δ⌋ ≠ ⌊y / δ⌋ := by
    intro he
    exact h (by simp only [rd, he])
  rw [Real.dist_eq, rd, rd, ← sub_mul, abs_mul, abs_of_pos hδ]
  have : (1 : ℝ) ≤ |((⌊x / δ⌋ : ℤ) : ℝ) - ((⌊y / δ⌋ : ℤ) : ℝ)| := by
    rw [← Int.cast_sub, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hne)
  nlinarith

lemma rd_mono {δ : ℝ} (hδ : 0 < δ) {x y : ℝ} (h : x ≤ y) : rd δ x ≤ rd δ y := by
  unfold rd
  have : ⌊x / δ⌋ ≤ ⌊y / δ⌋ := Int.floor_mono (div_le_div_of_nonneg_right h hδ.le)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) hδ.le

/-- Points within `δ` of `y` round to one of three grid points. -/
lemma rd_mem_three {δ : ℝ} (hδ : 0 < δ) {x y : ℝ} (h : |x - y| ≤ δ) :
    rd δ x ∈ ({rd δ (y - δ), rd δ (y - δ) + δ, rd δ (y - δ) + 2 * δ} : Finset ℝ) := by
  rw [abs_le] at h
  have hlo : rd δ (y - δ) ≤ rd δ x := rd_mono hδ (by linarith)
  have hk : ∃ k : ℤ, rd δ x - rd δ (y - δ) = (k : ℝ) * δ := by
    refine ⟨⌊x / δ⌋ - ⌊(y - δ) / δ⌋, ?_⟩
    simp only [rd, Int.cast_sub]
    ring
  obtain ⟨k, hk⟩ := hk
  have hup : rd δ x < rd δ (y - δ) + 3 * δ := by
    have h1 := rd_le hδ x
    have h2 := lt_rd_add hδ (y - δ)
    linarith
  have hk0 : (0 : ℝ) ≤ k * δ := by linarith
  have hk3 : (k : ℝ) * δ < 3 * δ := by linarith
  have hk0' : (0 : ℝ) ≤ k := by
    by_contra hc
    have hc' : (k : ℝ) < 0 := lt_of_not_ge hc
    nlinarith
  have hk3' : (k : ℝ) < 3 := by
    by_contra hc
    have hc' : (3 : ℝ) ≤ k := le_of_not_gt hc
    nlinarith
  have hk0'' : 0 ≤ k := by exact_mod_cast hk0'
  have hk3'' : k < 3 := by exact_mod_cast hk3'
  have hx : rd δ x = rd δ (y - δ) + (k : ℝ) * δ := by linarith
  interval_cases k <;> simp [hx]

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
