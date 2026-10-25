-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extreme_offset_fibre_estimate.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extreme_offset_fibre_estimate.Coordinates

namespace WangZahlLot.Obl.wz_extreme_offset_fibre_estimate

open MeasureTheory Set Metric

noncomputable section

/-- Horizontal coordinate of the axis at a prescribed height. -/
def axis (x v : Space) (z : ℝ) : ℝ := x 0 + (z - x 2) * (v 0 / v 2)

lemma measurable_axis (x v : Space) : Measurable (axis x v) := by
  unfold axis
  fun_prop

lemma transverse_ratio {v : Space} (hv : ‖v‖ = 1) (ht : (1 / 2 : ℝ) ≤ |v 2|) :
    |v 0 / v 2| ≤ 2 := by
  have h0 : |v 0| ≤ 1 := by simpa [hv, Real.norm_eq_abs] using PiLp.norm_apply_le v 0
  have h2 : 0 < |v 2| := by linarith
  rw [abs_div, div_le_iff₀ h2]
  linarith

lemma tube_horizontal_width {δ : ℝ} {x v p : Space}
    (hv : ‖v‖ = 1) (ht : (1 / 2 : ℝ) ≤ |v 2|)
    (hp : p ∈ thickening δ (segment ℝ x (x + v))) :
    |p 0 - axis x v (p 2)| ≤ 3 * δ := by
  have hv2 : v 2 ≠ 0 := by
    intro h
    simp only [h, abs_zero] at ht
    norm_num at ht
  have hr := transverse_ratio hv ht
  obtain ⟨q, hq, hd⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨t, ht', rfl⟩ := hq
  simp only [add_sub_cancel_left] at hd
  have he (j : Fin 3) : |p j - (x j + t * v j)| ≤ δ := by
    have hc := PiLp.norm_apply_le (p - (x + t • v)) j
    have hn : ‖p - (x + t • v)‖ < δ := by simpa only [dist_eq_norm] using hd
    simpa [Real.norm_eq_abs] using hc.trans hn.le
  have hδ : 0 ≤ δ := dist_nonneg.trans hd.le
  have halg : p 0 - axis x v (p 2) =
      (p 0 - (x 0 + t * v 0)) - (p 2 - (x 2 + t * v 2)) * (v 0 / v 2) := by
    unfold axis
    field_simp
    ring
  rw [halg]
  calc
    |p 0 - (x 0 + t * v 0) - (p 2 - (x 2 + t * v 2)) * (v 0 / v 2)|
        ≤ |p 0 - (x 0 + t * v 0)| + |p 2 - (x 2 + t * v 2)| * |v 0 / v 2| := by
      simpa only [abs_mul] using abs_sub (p 0 - (x 0 + t * v 0))
        ((p 2 - (x 2 + t * v 2)) * (v 0 / v 2))
    _ ≤ δ + δ * 2 := by gcongr <;> apply he
    _ = 3 * δ := by ring

lemma height_mem_Icc {p : Space} (hp : p ∈ ball (0 : Space) 1) :
    p 2 ∈ Icc (-1 : ℝ) 1 := by
  have hn : ‖p‖ < 1 := by simpa using hp
  have hc : |p 2| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le p 2).trans hn.le
  exact abs_le.mp hc

lemma slope_value_lower {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hd : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv f z| ≤ 2)
    {δ z : ℝ} (hoff : 2 + 6 / δ ≤ |f 0|) (hz : z ∈ Icc (-1 : ℝ) 1) :
    6 / δ ≤ |f z| := by
  have hdiff := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun y _ => (hf.differentiable (by norm_num)) y)
    (fun y hy => by simpa only [Real.norm_eq_abs] using hd y hy)
    (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num) hz
  have hdz : |f z - f 0| ≤ 2 := by
    have hz' : |z| ≤ 1 := abs_le.mpr hz
    simp only [Real.norm_eq_abs, sub_zero] at hdiff
    nlinarith
  have htri := abs_sub_abs_le_abs_sub (f 0) (f z)
  rw [abs_sub_comm (f 0)] at htri
  linarith

lemma centeredChart_fibre_bound {δ : ℝ} (hδ : 0 < δ) {f : ℝ → ℝ} {x v p : Space}
    (hf : 6 / δ ≤ |f (p 2)|) (hw : |p 0 - axis x v (p 2)| ≤ 3 * δ) :
    |(centeredChart f (axis x v) p).2| ≤ δ ^ 2 / 2 := by
  have hfp : 0 < |f (p 2)| := lt_of_lt_of_le (div_pos (by norm_num) hδ) hf
  have hfn : f (p 2) ≠ 0 := abs_pos.mp hfp
  have hid : (centeredChart f (axis x v) p).2 =
      -(p 0 - axis x v (p 2)) / f (p 2) := by
    dsimp [centeredChart, chart]
    field_simp
    ring
  rw [hid, abs_div, abs_neg, div_le_iff₀ hfp]
  have hmul : 6 ≤ |f (p 2)| * δ := (div_le_iff₀ hδ).mp hf
  nlinarith [mul_le_mul_of_nonneg_right hmul (show 0 ≤ δ / 2 by positivity)]

end

end WangZahlLot.Obl.wz_extreme_offset_fibre_estimate
