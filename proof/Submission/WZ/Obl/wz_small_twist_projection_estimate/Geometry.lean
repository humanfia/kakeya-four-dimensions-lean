-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_small_twist_projection_estimate.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
/-!
# Tube geometry at a fixed height

For a transverse tube, every point lies within `3δ` of the axis point at its own height.
Consequently two points of a tube at the same height are within `6δ`, the twisted coordinate
of a tube point is close to that of the axis, and the horizontal grain fibres of a tube are
short.
-/

namespace WangZahlLot.Obl.wz_small_twist_projection_estimate

open Set Metric MeasureTheory
open scoped ENNReal

abbrev Space := LeanEval.Analysis.WangZahlKakeya.Space

/-- The tube of the frozen statement. -/
abbrev tube (δ : ℝ) (x v : Space) : Set Space :=
  Metric.thickening δ (segment ℝ x (x + v))

/-- The point of the line through `x` with direction `v` at height `z`. -/
noncomputable def lineAt (x v : Space) (z : ℝ) : Space := x + ((z - x 2) / v 2) • v

lemma coord_abs_le (p : Space) (i : Fin 3) : |p i| ≤ ‖p‖ := by
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le p i

lemma v2_ne_zero {v : Space} (hv2 : (1 / 2 : ℝ) ≤ |v 2|) : v 2 ≠ 0 := by
  intro h
  rw [h, abs_zero] at hv2
  norm_num at hv2

lemma lineAt_two {x v : Space} (hv2 : v 2 ≠ 0) (z : ℝ) : lineAt x v z 2 = z := by
  simp only [lineAt, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

lemma lineAt_sub_lineAt (x v : Space) (s t : ℝ) :
    lineAt x v s - lineAt x v t = ((s - t) / v 2) • v := by
  simp only [lineAt]
  rw [add_sub_add_left_eq_sub, ← sub_smul]
  congr 1
  ring

/-- Every point of a transverse tube lies within `3δ` of the axis point at its height. -/
lemma norm_sub_lineAt_lt {δ : ℝ} {x v p : Space} (hv : ‖v‖ = 1)
    (hv2 : (1 / 2 : ℝ) ≤ |v 2|) (hp : p ∈ tube δ x v) :
    ‖p - lineAt x v (p 2)‖ < 3 * δ := by
  have hv0 := v2_ne_zero hv2
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨t, -, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq ⊢
  have hq2 : lineAt x v ((x + t • v) 2) = x + t • v := by
    simp only [lineAt, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    congr 2
    field_simp
    ring
  have hcoord : |p 2 - (x + t • v) 2| ≤ dist p (x + t • v) := by
    have h := coord_abs_le (p - (x + t • v)) 2
    rwa [PiLp.sub_apply, ← dist_eq_norm] at h
  have hL' : ‖lineAt x v (p 2) - lineAt x v ((x + t • v) 2)‖ ≤ 2 * dist p (x + t • v) := by
    rw [lineAt_sub_lineAt, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_div,
      div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg (p 2 - (x + t • v) 2), dist_nonneg (x := p) (y := x + t • v)]
  have hL : ‖lineAt x v (p 2) - (x + t • v)‖ ≤ 2 * dist p (x + t • v) := by
    rwa [hq2] at hL'
  have heq : p - lineAt x v (p 2) = (p - (x + t • v)) - (lineAt x v (p 2) - (x + t • v)) := by
    abel
  rw [heq]
  calc ‖(p - (x + t • v)) - (lineAt x v (p 2) - (x + t • v))‖
      ≤ ‖p - (x + t • v)‖ + ‖lineAt x v (p 2) - (x + t • v)‖ := norm_sub_le _ _
    _ < 3 * δ := by rw [← dist_eq_norm]; linarith

/-- The axis point at a height in `[-1, 1]` of a tube inside the unit ball is bounded. -/
lemma norm_lineAt_le {δ : ℝ} (hδ : 0 < δ) {x v : Space} (hv : ‖v‖ = 1)
    (hv2 : (1 / 2 : ℝ) ≤ |v 2|) (hT : tube δ x v ⊆ ball 0 1) {z : ℝ} (hz : |z| ≤ 1) :
    ‖lineAt x v z‖ ≤ 5 := by
  have hx : x ∈ tube δ x v := self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v))
  have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp (hT hx)
  have hx2 : |x 2| ≤ 1 := (coord_abs_le x 2).trans hx1.le
  have hzx : |z - x 2| ≤ 2 := (abs_sub _ _).trans (by linarith)
  have hv0 : 0 < |v 2| := by linarith
  have hdiv : |z - x 2| / |v 2| ≤ 4 := by
    rw [div_le_iff₀ hv0]
    linarith
  calc ‖lineAt x v z‖ ≤ ‖x‖ + ‖((z - x 2) / v 2) • v‖ := norm_add_le _ _
    _ = ‖x‖ + |z - x 2| / |v 2| := by rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_div]
    _ ≤ 5 := by linarith

/-- Two points of a transverse tube at the same height are within `6δ`. -/
lemma norm_sub_lt_of_same_height {δ : ℝ} {x v p q : Space} (hv : ‖v‖ = 1)
    (hv2 : (1 / 2 : ℝ) ≤ |v 2|) (hp : p ∈ tube δ x v) (hq : q ∈ tube δ x v)
    (hpq : p 2 = q 2) : ‖p - q‖ < 6 * δ := by
  have h1 := norm_sub_lineAt_lt hv hv2 hp
  have h2 := norm_sub_lineAt_lt hv hv2 hq
  rw [hpq] at h1
  calc ‖p - q‖ = ‖(p - lineAt x v (q 2)) - (q - lineAt x v (q 2))‖ := by congr 1; abel
    _ ≤ ‖p - lineAt x v (q 2)‖ + ‖q - lineAt x v (q 2)‖ := norm_sub_le _ _
    _ < 6 * δ := by linarith

/-- The twisted coordinate of a tube point is close to the twisted coordinate of the axis
point at its height. -/
lemma twist_sub_lineAt_lt {δ M : ℝ} {x v p : Space} {f : ℝ → ℝ} (hv : ‖v‖ = 1)
    (hv2 : (1 / 2 : ℝ) ≤ |v 2|) (hp : p ∈ tube δ x v) (hM : |f (p 2)| ≤ M) :
    |(p 0 + f (p 2) * p 1) - (lineAt x v (p 2) 0 + f (p 2) * lineAt x v (p 2) 1)| ≤
      3 * δ * (1 + M) := by
  have h := norm_sub_lineAt_lt hv hv2 hp
  set q := lineAt x v (p 2)
  have h0 : |p 0 - q 0| ≤ ‖p - q‖ := by
    have := coord_abs_le (p - q) 0
    rwa [PiLp.sub_apply] at this
  have h1 : |p 1 - q 1| ≤ ‖p - q‖ := by
    have := coord_abs_le (p - q) 1
    rwa [PiLp.sub_apply] at this
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  have heq : (p 0 + f (p 2) * p 1) - (q 0 + f (p 2) * q 1) =
      (p 0 - q 0) + f (p 2) * (p 1 - q 1) := by ring
  rw [heq]
  calc |(p 0 - q 0) + f (p 2) * (p 1 - q 1)| ≤ |p 0 - q 0| + |f (p 2)| * |p 1 - q 1| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ ‖p - q‖ + M * ‖p - q‖ := by
        gcongr
    _ = (1 + M) * ‖p - q‖ := by ring
    _ ≤ (1 + M) * (3 * δ) := by gcongr
    _ = 3 * δ * (1 + M) := by ring

end WangZahlLot.Obl.wz_small_twist_projection_estimate
