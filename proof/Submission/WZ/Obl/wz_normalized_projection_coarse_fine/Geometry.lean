-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

abbrev Tube (δ : ℝ) (x v : Space) : Set Space :=
  thickening δ (segment ℝ x (x + v))

def projection (f : ℝ → ℝ) (p : Space) : ℝ × ℝ :=
  (p 0 + f (p 2) * p 1, p 2)

def slope (v : Space) (i : Fin 3) : ℝ := v i / v 2

def intercept (x v : Space) (i : Fin 3) : ℝ := x i - slope v i * x 2

def parameters (x v : Space) : Space :=
  WithLp.toLp 2 ![intercept x v 0, intercept x v 1, slope v 1]

def lineParameters (x v : Space) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![intercept x v 0, intercept x v 1, slope v 0, slope v 1]

lemma abs_coordinate_le_norm (p : Space) (i : Fin 3) : |p i| ≤ ‖p‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p i

lemma abs_coordinate_sub_le_dist (p q : Space) (i : Fin 3) :
    |p i - q i| ≤ dist p q := by
  simpa only [Real.dist_eq] using PiLp.dist_apply_le p q i

lemma abs_slope_le_two {v : Space} (hv : ‖v‖ = 1)
    (htrans : (1 / 2 : ℝ) ≤ |v 2|) (i : Fin 3) : |slope v i| ≤ 2 := by
  have hpos : 0 < |v 2| := lt_of_lt_of_le (by norm_num) htrans
  rw [slope, abs_div, div_le_iff₀ hpos]
  have hcoord := abs_coordinate_le_norm v i
  rw [hv] at hcoord
  linarith

lemma abs_intercept_le_three {x v : Space} (hx : ‖x‖ ≤ 1) (hv : ‖v‖ = 1)
    (htrans : (1 / 2 : ℝ) ≤ |v 2|) (i : Fin 3) : |intercept x v i| ≤ 3 := by
  calc
    |intercept x v i| ≤ |x i| + |slope v i * x 2| := abs_sub _ _
    _ = |x i| + |slope v i| * |x 2| := by rw [abs_mul]
    _ ≤ 1 + 2 * 1 := by
      gcongr
      · exact (abs_coordinate_le_norm x i).trans hx
      · exact abs_slope_le_two hv htrans i
      · exact (abs_coordinate_le_norm x 2).trans hx
    _ = 3 := by norm_num

lemma parameters_norm_le_five {x v : Space} (hx : ‖x‖ ≤ 1) (hv : ‖v‖ = 1)
    (htrans : (1 / 2 : ℝ) ≤ |v 2|) : ‖parameters x v‖ ≤ 5 := by
  have ha := abs_intercept_le_three hx hv htrans 0
  have hb := abs_intercept_le_three hx hv htrans 1
  have hd := abs_slope_le_two hv htrans 1
  have hsq := EuclideanSpace.real_norm_sq_eq (parameters x v)
  simp only [Fin.sum_univ_three] at hsq
  change ‖parameters x v‖ ^ 2 =
    intercept x v 0 ^ 2 + intercept x v 1 ^ 2 + slope v 1 ^ 2 at hsq
  have ha2 := mul_self_le_mul_self (abs_nonneg _) ha
  have hb2 := mul_self_le_mul_self (abs_nonneg _) hb
  have hd2 := mul_self_le_mul_self (abs_nonneg _) hd
  nlinarith [sq_abs (intercept x v 0), sq_abs (intercept x v 1), sq_abs (slope v 1),
    norm_nonneg (parameters x v)]

lemma line_coordinate {x v : Space} (hv : v 2 ≠ 0) (t : ℝ) (i : Fin 3) :
    (x + t • v) i = intercept x v i + slope v i * (x + t • v) 2 := by
  simp only [intercept, slope, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp
  ring

lemma tube_coordinate_bound {δ : ℝ} {x v p : Space} (hv : ‖v‖ = 1)
    (htrans : (1 / 2 : ℝ) ≤ |v 2|) (hp : p ∈ Tube δ x v) (i : Fin 3) :
    |p i - (intercept x v i + slope v i * p 2)| < 3 * δ := by
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq ⊢
  have hv2 : v 2 ≠ 0 := by
    intro h
    norm_num [h] at htrans
  have hcoord := line_coordinate (x := x) hv2 t i
  have hdist0 := (abs_coordinate_sub_le_dist p (x + t • v) i).trans_lt hpq
  have hdist2 := (abs_coordinate_sub_le_dist p (x + t • v) 2).trans_lt hpq
  have hδ : 0 < δ := (dist_nonneg).trans_lt hpq
  calc
    |p i - (intercept x v i + slope v i * p 2)| =
        |(p i - (x + t • v) i) - slope v i * (p 2 - (x + t • v) 2)| := by
      congr 1
      rw [hcoord]
      ring
    _ ≤ |p i - (x + t • v) i| + |slope v i| * |p 2 - (x + t • v) 2| := by
      simpa only [abs_mul] using abs_sub (p i - (x + t • v) i)
        (slope v i * (p 2 - (x + t • v) 2))
    _ ≤ |p i - (x + t • v) i| + 2 * δ := by
      gcongr
      exact abs_slope_le_two hv htrans i
    _ < 3 * δ := by linarith

lemma slope_lipschitz_on {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hderiv : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv f z| ≤ 2)
    {z w : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) (hw : w ∈ Icc (-1 : ℝ) 1) :
    |f z - f w| ≤ 2 * |z - w| := by
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun x _ => (hf.differentiable (by norm_num)).differentiableAt)
      (fun x hx => by simpa only [Real.norm_eq_abs] using hderiv x hx) hw hz

lemma normalized_slope_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hderiv : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv f z| ≤ 2) (hf0 : |f 0| ≤ 1)
    {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) : |f z| ≤ 3 := by
  have hzabs : |z| ≤ 1 := abs_le.mpr hz
  have hdiff := slope_lipschitz_on hf hderiv hz (show 0 ∈ Icc (-1 : ℝ) 1 by norm_num)
  simp only [sub_zero] at hdiff
  calc
    |f z| ≤ |f z - f 0| + |f 0| := by
      simpa only [sub_add_cancel] using abs_add_le (f z - f 0) (f 0)
    _ ≤ 2 * 1 + 1 := by gcongr; exact hdiff.trans (by gcongr)
    _ = 3 := by norm_num

lemma tube_projection_bound {δ : ℝ} {x v p : Space} (hv : ‖v‖ = 1)
    (htrans : (1 / 2 : ℝ) ≤ |v 2|) (hp : p ∈ Tube δ x v)
    {f : ℝ → ℝ} (hf : |f (p 2)| ≤ 3) :
    |(projection f p).1 - (intercept x v 0 + slope v 0 * p 2 +
      intercept x v 1 * f (p 2) + slope v 1 * p 2 * f (p 2))| < 12 * δ := by
  have h0 := tube_coordinate_bound hv htrans hp 0
  have h1 := tube_coordinate_bound hv htrans hp 1
  calc
    _ = |(p 0 - (intercept x v 0 + slope v 0 * p 2)) +
      f (p 2) * (p 1 - (intercept x v 1 + slope v 1 * p 2))| := by
        congr 1
        simp only [projection]
        ring
    _ ≤ |p 0 - (intercept x v 0 + slope v 0 * p 2)| +
      |f (p 2)| * |p 1 - (intercept x v 1 + slope v 1 * p 2)| := by
        simpa only [abs_mul] using abs_add_le
          (p 0 - (intercept x v 0 + slope v 0 * p 2))
          (f (p 2) * (p 1 - (intercept x v 1 + slope v 1 * p 2)))
    _ ≤ |p 0 - (intercept x v 0 + slope v 0 * p 2)| + 3 * (3 * δ) := by
        gcongr
    _ < 12 * δ := by linarith

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
