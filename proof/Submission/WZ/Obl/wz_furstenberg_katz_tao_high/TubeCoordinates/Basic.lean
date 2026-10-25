-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Ported from workspace o157, branch x0572 (commit 9dec67f), TubeCoordinates/Basic.lean;
-- SP references re-pointed to the accepted o223 (SP), o142 (covers) and o143 (cover counting) modules.
import Mathlib

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates


/-- An affine line is represented by its slope and intercept. -/
def height (l : ℝ × ℝ) (x : ℝ) : ℝ := l.1 * x + l.2

/-- Heights on a line interpolate affinely between two columns. -/
lemma height_interpolate (l : ℝ × ℝ) (x₀ x₁ t : ℝ) :
    height l ((1 - t) * x₀ + t * x₁) =
      (1 - t) * height l x₀ + t * height l x₁ := by
  unfold height
  ring

lemma height_difference (l l' : ℝ × ℝ) (x₀ x₁ : ℝ) :
    (height l x₁ - height l' x₁) - (height l x₀ - height l' x₀) =
      (l.1 - l'.1) * (x₁ - x₀) := by
  unfold height
  ring

/-- Two distinct columns determine a line. -/
lemma heights_injective {x₀ x₁ : ℝ} (hgap : x₀ ≠ x₁) :
    Function.Injective (fun l : ℝ × ℝ => (height l x₀, height l x₁)) := by
  intro l l' h
  obtain ⟨h₀, h₁⟩ := Prod.mk.inj h
  have ha : l.1 = l'.1 := by
    have hz := height_difference l l' x₀ x₁
    rw [h₀, h₁, sub_self, sub_self, sub_self] at hz
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz.symm).resolve_right (sub_ne_zero.mpr hgap.symm))
  apply Prod.ext ha
  dsimp [height] at h₀
  rw [ha] at h₀
  linarith

/-- Small changes in the two heights control both affine parameters. -/
lemma parameters_close_of_heights {l l' : ℝ × ℝ} {x₀ x₁ q h B : ℝ}
    (hq : 0 < q) (hgap : q ≤ |x₁ - x₀|) (hx : |x₀| ≤ B)
    (h₀ : |height l x₀ - height l' x₀| < h)
    (h₁ : |height l x₁ - height l' x₁| < h) :
    |l.1 - l'.1| < 2 * h / q ∧
      |l.2 - l'.2| < h + B * (2 * h / q) := by
  have hh : 0 < h := (abs_nonneg _).trans_lt h₀
  have hB : 0 ≤ B := (abs_nonneg _).trans hx
  have hprod : |l.1 - l'.1| * q < 2 * h := by
    calc
      |l.1 - l'.1| * q ≤ |l.1 - l'.1| * |x₁ - x₀| := by gcongr
      _ = |(height l x₁ - height l' x₁) - (height l x₀ - height l' x₀)| := by
        rw [height_difference, abs_mul]
      _ ≤ |height l x₁ - height l' x₁| + |height l x₀ - height l' x₀| := abs_sub _ _
      _ < 2 * h := by linarith
  have hs : |l.1 - l'.1| < 2 * h / q := (lt_div_iff₀ hq).mpr hprod
  refine ⟨hs, ?_⟩
  calc
    |l.2 - l'.2| = |(height l x₀ - height l' x₀) - (l.1 - l'.1) * x₀| := by
      congr 1
      unfold height
      ring
    _ ≤ |height l x₀ - height l' x₀| + |(l.1 - l'.1) * x₀| := abs_sub _ _
    _ ≤ |height l x₀ - height l' x₀| + |l.1 - l'.1| * B := by rw [abs_mul]; gcongr
    _ < h + (2 * h / q) * B := add_lt_add_of_lt_of_le h₀ (by gcongr)
    _ = _ := by ring

/-- Replacing the horizontal position of an incident point by its column center
costs the product of the slope bound and the column width. -/
lemma height_at_column {l : ℝ × ℝ} {x y c r Δ A : ℝ}
    (hinc : |y - height l x| ≤ r) (hcolumn : |x - c| ≤ Δ)
    (hslope : |l.1| ≤ A) :
    |y - height l c| ≤ r + A * Δ := by
  have hΔ : 0 ≤ Δ := (abs_nonneg _).trans hcolumn
  calc
    |y - height l c| = |(y - height l x) + l.1 * (x - c)| := by
      congr 1
      unfold height
      ring
    _ ≤ |y - height l x| + |l.1 * (x - c)| := abs_add_le _ _
    _ = |y - height l x| + |l.1| * |x - c| := by rw [abs_mul]
    _ ≤ r + A * Δ := add_le_add hinc
      (mul_le_mul hslope hcolumn (abs_nonneg _) ((abs_nonneg _).trans hslope))

/-- Scaling only the transverse coordinate rescales both affine parameters. -/
noncomputable def rescale (Δ : ℝ) (l : ℝ × ℝ) : ℝ × ℝ := (l.1 / Δ, l.2 / Δ)

lemma height_rescale (Δ : ℝ) (l : ℝ × ℝ) (x : ℝ) :
    height (rescale Δ l) x = height l x / Δ := by
  unfold height rescale
  ring

/-- The error at the column center after transverse rescaling. -/
lemma rescaled_column_incidence {l : ℝ × ℝ} {x y c r Δ : ℝ}
    (hΔ : 0 < Δ) (hinc : |y - height l x| ≤ r)
    (hcolumn : |x - c| ≤ Δ) (hslope : |l.1| ≤ Δ) :
    |y / Δ - height (rescale Δ l) c| ≤ r / Δ + Δ := by
  rw [height_rescale, ← sub_div, abs_div, abs_of_pos hΔ]
  have hh := div_le_div_of_nonneg_right (height_at_column hinc hcolumn hslope) hΔ.le
  convert hh using 1 <;> field_simp

/-- The column width may be chosen independently of the transverse scale.
The product of width and slope bound controls the freezing error. -/
lemma rescaled_column_incidence_of_width {l : ℝ × ℝ} {x y c r Δ w : ℝ}
    (hΔ : 0 < Δ) (hscale : Δ * w ≤ r) (hinc : |y - height l x| ≤ r)
    (hcolumn : |x - c| ≤ w) (hslope : |l.1| ≤ Δ) :
    |y / Δ - height (rescale Δ l) c| ≤ 2 * (r / Δ) := by
  rw [height_rescale, ← sub_div, abs_div, abs_of_pos hΔ]
  have hb : |y - height l c| ≤ 2 * r :=
    (height_at_column hinc hcolumn hslope).trans (by linarith)
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hb hΔ.le

/-- At a square-root-or-finer coarse scale, column freezing costs at most
one additional fine-scale radius after rescaling. -/
lemma rescaled_column_incidence_two {l : ℝ × ℝ} {x y c r Δ : ℝ}
    (hΔ : 0 < Δ) (hscale : Δ ^ 2 ≤ r) (hinc : |y - height l x| ≤ r)
    (hcolumn : |x - c| ≤ Δ) (hslope : |l.1| ≤ Δ) :
    |y / Δ - height (rescale Δ l) c| ≤ 2 * (r / Δ) := by
  have hh := rescaled_column_incidence hΔ hinc hcolumn hslope
  have hΔr : Δ ≤ r / Δ := (le_div_iff₀ hΔ).mpr (by nlinarith)
  linarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates
