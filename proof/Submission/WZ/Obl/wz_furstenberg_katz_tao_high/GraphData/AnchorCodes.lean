-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData.AnchorCodes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o214/x0665 WangZahlLot/Obl/wz_furstenberg_katz_tao_high/GraphData/AnchorCodes.lean (82de8bd).
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.Charts

/-!
# Anchor codes of affine lines

A line is a pair `l = (c, a)` with height `lineHeight l x = a + c x`.  For two anchor positions
`x₀ ≠ x₁` its anchor code is `anchorCode x₀ x₁ l = (lineHeight l x₀, lineHeight l x₁)`, and the
column at position `x` corresponds to the parameter `anchorParam x₀ x₁ x = (x - x₀) / (x₁ - x₀)`.

* `hgt_anchorCode`: `hgt (anchorCode x₀ x₁ l) (anchorParam x₀ x₁ x) = lineHeight l x` (x0658's
  `hgt w τ = (1 - τ) w.1 + τ w.2`).
* `anchorCode_close`: if the anchors are `q` apart and `|x₀| ≤ 4`, two lines whose codes are within
  `D` in both coordinates have parameters within `9 D / q` (for `q ≤ 1`).
* `anchorCode_sep`: hence parameters `σ`-separated in the sup sense give codes `q σ / 9`-separated.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

/-- Height of the line `l = (c, a)` at `x`. -/
def lineHeight (l : ℝ × ℝ) (x : ℝ) : ℝ := l.2 + l.1 * x

/-- The anchor code of a line. -/
def anchorCode (x₀ x₁ : ℝ) (l : ℝ × ℝ) : ℝ × ℝ := (lineHeight l x₀, lineHeight l x₁)

/-- The anchor parameter of a column position. -/
noncomputable def anchorParam (x₀ x₁ x : ℝ) : ℝ := (x - x₀) / (x₁ - x₀)

theorem hgt_anchorCode {x₀ x₁ : ℝ} (h : x₀ ≠ x₁) (l : ℝ × ℝ) (x : ℝ) :
    hgt (anchorCode x₀ x₁ l) (anchorParam x₀ x₁ x) = lineHeight l x := by
  have hne : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  simp only [hgt, anchorCode, anchorParam, lineHeight]
  field_simp
  ring

/-- The anchor parameter is injective. -/
theorem anchorParam_injective {x₀ x₁ : ℝ} (h : x₀ ≠ x₁) :
    Function.Injective (anchorParam x₀ x₁) := by
  intro x y hxy
  have hne : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  simp only [anchorParam] at hxy
  field_simp at hxy
  linarith

/-- Parameters are controlled by codes. -/
theorem anchorCode_close {x₀ x₁ q D : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hgap : q ≤ |x₁ - x₀|)
    (hx₀ : |x₀| ≤ 4) {l l' : ℝ × ℝ}
    (hu : |lineHeight l x₀ - lineHeight l' x₀| ≤ D) (hv : |lineHeight l x₁ - lineHeight l' x₁| ≤ D) :
    |l.1 - l'.1| ≤ 9 * D / q ∧ |l.2 - l'.2| ≤ 9 * D / q := by
  have hD : 0 ≤ D := le_trans (abs_nonneg _) hu
  have hgap0 : 0 < |x₁ - x₀| := lt_of_lt_of_le hq hgap
  have hc : (l.1 - l'.1) * (x₁ - x₀) =
      (lineHeight l x₁ - lineHeight l' x₁) - (lineHeight l x₀ - lineHeight l' x₀) := by
    simp only [lineHeight]; ring
  have hcabs : |l.1 - l'.1| * |x₁ - x₀| ≤ 2 * D := by
    rw [← abs_mul, hc]
    calc |(lineHeight l x₁ - lineHeight l' x₁) - (lineHeight l x₀ - lineHeight l' x₀)|
        ≤ |lineHeight l x₁ - lineHeight l' x₁| + |lineHeight l x₀ - lineHeight l' x₀| :=
          abs_sub _ _
      _ ≤ 2 * D := by linarith
  have hc1 : |l.1 - l'.1| ≤ 2 * D / q := by
    rw [le_div_iff₀ hq]
    calc |l.1 - l'.1| * q ≤ |l.1 - l'.1| * |x₁ - x₀| :=
          mul_le_mul_of_nonneg_left hgap (abs_nonneg _)
      _ ≤ 2 * D := hcabs
  have ha : l.2 - l'.2 = (lineHeight l x₀ - lineHeight l' x₀) - (l.1 - l'.1) * x₀ := by
    simp only [lineHeight]; ring
  have hq9 : 2 * D / q ≤ 9 * D / q := by
    apply div_le_div_of_nonneg_right _ hq.le; linarith
  refine ⟨hc1.trans hq9, ?_⟩
  rw [ha]
  have hDq : D ≤ D / q := by
    rw [le_div_iff₀ hq]; nlinarith
  calc |(lineHeight l x₀ - lineHeight l' x₀) - (l.1 - l'.1) * x₀|
      ≤ |lineHeight l x₀ - lineHeight l' x₀| + |(l.1 - l'.1) * x₀| := abs_sub _ _
    _ ≤ D + (2 * D / q) * 4 := by
        rw [abs_mul]
        have := mul_le_mul hc1 hx₀ (abs_nonneg _) (by positivity)
        linarith
    _ ≤ 9 * D / q := by
        have : D + 2 * D / q * 4 = D + 8 * D / q := by ring
        rw [this]
        have h8 : 8 * D / q + D / q = 9 * D / q := by ring
        linarith

/-- Parameters `σ`-separated (in the sup sense) give codes `q σ / 9`-separated. -/
theorem anchorCode_sep {x₀ x₁ q σ : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hgap : q ≤ |x₁ - x₀|)
    (hx₀ : |x₀| ≤ 4) {l l' : ℝ × ℝ}
    (hsep : σ ≤ |l.1 - l'.1| ∨ σ ≤ |l.2 - l'.2|) :
    q * σ / 9 ≤ dist (anchorCode x₀ x₁ l) (anchorCode x₀ x₁ l') := by
  set D := dist (anchorCode x₀ x₁ l) (anchorCode x₀ x₁ l') with hDdef
  have hu : |lineHeight l x₀ - lineHeight l' x₀| ≤ D := by
    rw [hDdef, Prod.dist_eq]
    have : |lineHeight l x₀ - lineHeight l' x₀| =
        dist (anchorCode x₀ x₁ l).1 (anchorCode x₀ x₁ l').1 := by
      simp [anchorCode, Real.dist_eq]
    rw [this]; exact le_max_left _ _
  have hv : |lineHeight l x₁ - lineHeight l' x₁| ≤ D := by
    rw [hDdef, Prod.dist_eq]
    have : |lineHeight l x₁ - lineHeight l' x₁| =
        dist (anchorCode x₀ x₁ l).2 (anchorCode x₀ x₁ l').2 := by
      simp [anchorCode, Real.dist_eq]
    rw [this]; exact le_max_right _ _
  obtain ⟨h1, h2⟩ := anchorCode_close hq hq1 hgap hx₀ hu hv
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 9)]
  rcases hsep with h | h
  · have : σ ≤ 9 * D / q := h.trans h1
    rw [le_div_iff₀ hq] at this; linarith
  · have : σ ≤ 9 * D / q := h.trans h2
    rw [le_div_iff₀ hq] at this; linarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
