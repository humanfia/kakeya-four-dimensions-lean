-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.FarTransversal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.MidDefs

/-!
# Refined transversality of far pairs

For two transverse unit tubes, `h(z) = ctr_1(z) - ctr_2(z)` (difference of the twisted centres)
has derivative `h' = f·ΔslX - B (f - c)/c + f'·Δy`, where `B` is the difference of the
`x`-slopes and `Δy` the (affine) difference of the `y`-coordinates of the axes. Where both
fibres meet, `|h| ≤ 6δ(|c|+3)` and `|Δy| ≤ (6δ(|c|+3) + 10)/(|c|-2)`. Hence, if the slopes of
the slab coordinate differ by at least `100/c²` and `δ c² ≤ 1`, then `|h'| ≥ 0.69 |c| |ΔslX|`
between any two such heights, and the mean value theorem bounds the length of the height set
`Z2` by `18 δ / |ΔslX|`. This replaces the bound `2κ/|ΔslX|` with `κ ~ δ + c⁻²` and keeps the
fine scale `δ` for far pairs.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space tube SlopeN lineAt ctr slX Xc
  coord_abs_le v2_ne_zero norm_lineAt_le)

lemma lineAt_apply (x v : Space) (z : ℝ) (i : Fin 3) :
    lineAt x v z i = x i + (z - x 2) / v 2 * v i := by
  simp [lineAt, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

lemma hasDerivAt_lineAt (x v : Space) (i : Fin 3) (z : ℝ) :
    HasDerivAt (fun z => lineAt x v z i) (v i / v 2) z := by
  have he : (fun z => lineAt x v z i) = fun z => x i + (z - x 2) / v 2 * v i := by
    funext w
    exact lineAt_apply x v w i
  rw [he]
  have h1 : HasDerivAt (fun w : ℝ => (w - x 2) / v 2 * v i) (1 / v 2 * v i) z :=
    (((hasDerivAt_id z).sub_const (x 2)).div_const (v 2)).mul_const (v i)
  have h2 := h1.const_add (x i)
  convert h2 using 1
  ring

/-- The difference of the twisted centres as a function of the height. -/
lemma ctr_sub_eq (f : ℝ → ℝ) (x v x' v' : Space) (z : ℝ) :
    ctr f x v z - ctr f x' v' z =
      (lineAt x v z 0 - lineAt x' v' z 0) + f z * (lineAt x v z 1 - lineAt x' v' z 1) := by
  simp only [ctr]
  ring

lemma slX_sub_eq {c : ℝ} (hc : c ≠ 0) (v v' : Space) :
    slX c v - slX c v' = (v 0 / v 2 - v' 0 / v' 2) / c + (v 1 / v 2 - v' 1 / v' 2) := by
  simp only [slX, Xc]
  field_simp
  ring

/-- An affine function on an interval is bounded by its values at the endpoints. -/
lemma abs_affine_le_max {α E z1 z2 ξ : ℝ} (h1 : z1 ≤ ξ) (h2 : ξ ≤ z2) :
    |α + E * ξ| ≤ max |α + E * z1| |α + E * z2| := by
  rcases le_total 0 E with hE | hE
  · exact abs_le_max_abs_abs (by nlinarith) (by nlinarith)
  · rw [max_comm]
    exact abs_le_max_abs_abs (by nlinarith) (by nlinarith)


/-- Arithmetic for the error terms of the derivative. -/
lemma far_err_arith {c B F d a w0 S : ℝ} (hc : 100 < |c|) (hB : |B| ≤ 4) (hF : |F - c| ≤ 2)
    (hd : |d| ≤ 2) (ha : |a| ≤ (w0 + 10) / (|c| - 2)) (hw0 : w0 ≤ 62 / 1000)
    (hcS : 100 ≤ c ^ 2 * |S|) :
    |B * (F - c) / c| + |d * a| ≤ 286 / 1000 * |c| * |S| := by
  have hc0 : 0 < |c| := by linarith
  have hcpos : 0 < |c| - 2 := by linarith
  have e1 : |B * (F - c) / c| ≤ 8 / |c| := by
    rw [abs_div, abs_mul]
    apply div_le_div_of_nonneg_right _ hc0.le
    calc |B| * |F - c| ≤ 4 * 2 := mul_le_mul hB hF (abs_nonneg _) (by norm_num)
      _ = 8 := by norm_num
  have e2 : |d * a| ≤ 2 * ((w0 + 10) / (|c| - 2)) := by
    rw [abs_mul]
    exact mul_le_mul hd ha (abs_nonneg _) (by norm_num)
  have e3 : 2 * ((w0 + 10) / (|c| - 2)) ≤ 206 / 10 / |c| := by
    rw [mul_div_assoc', div_le_div_iff₀ hcpos hc0]
    nlinarith
  have hcc : |c| * |c| = c ^ 2 := by rw [← sq, sq_abs]
  have e4 : (8 : ℝ) / |c| + 206 / 10 / |c| ≤ 286 / 1000 * |c| * |S| := by
    rw [← add_div, div_le_iff₀ hc0]
    have : 286 / 1000 * |c| * |S| * |c| = 286 / 1000 * (c ^ 2 * |S|) := by
      rw [← hcc]; ring
    rw [this]
    linarith
  linarith

/-- Arithmetic lower bound for the derivative. -/
lemma far_low_arith {c F S D e : ℝ} (hc : 100 < |c|) (hF : |c| - 2 ≤ |F|)
    (hrev : |F * S| ≤ |D| + e) (he : e ≤ 286 / 1000 * |c| * |S|) :
    69 / 100 * |c| * |S| ≤ |D| := by
  have hS := abs_nonneg S
  have h1 : (|c| - 2) * |S| ≤ |F * S| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hF hS
  have h2 : 2 * |S| ≤ 2 / 100 * |c| * |S| := by
    have : (2 : ℝ) ≤ 2 / 100 * |c| := by linarith
    calc 2 * |S| ≤ 2 / 100 * |c| * |S| := mul_le_mul_of_nonneg_right this hS
      _ = 2 / 100 * |c| * |S| := rfl
  nlinarith

set_option maxHeartbeats 800000 in
/-- **Refined transversality.** -/
theorem volume_Z2_le_of_slope {δ : ℝ} (hδ : 0 < δ) {f : ℝ → ℝ} (hf : SlopeN f)
    (hc : 100 < |f 0|) (hδc : δ * (f 0) ^ 2 ≤ 1)
    {x v x' v' : Space} (hv : ‖v‖ = 1) (hv2 : (1 / 2 : ℝ) ≤ |v 2|)
    (hT : tube δ x v ⊆ ball 0 1) (hv' : ‖v'‖ = 1) (hv2' : (1 / 2 : ℝ) ≤ |v' 2|)
    (hT' : tube δ x' v' ⊆ ball 0 1)
    (hB : 100 / (f 0) ^ 2 ≤ |slX (f 0) v - slX (f 0) v'|) :
    volume (Z2 f δ x v x' v') ≤ ENNReal.ofReal (18 * δ / |slX (f 0) v - slX (f 0) v'|) := by
  set c := f 0 with hcdef
  set S := slX c v - slX c v' with hSdef
  have hc0 : 0 < |c| := by linarith
  have hcne : c ≠ 0 := abs_pos.mp hc0
  have hc2 : 0 < c ^ 2 := by positivity
  have hS0 : 0 < |S| := lt_of_lt_of_le (by positivity) hB
  have hv0 := v2_ne_zero hv2
  have hv0' := v2_ne_zero hv2'
  have hd : Differentiable ℝ f := hf.1.differentiable (by norm_num)
  -- the constants
  set w0 := 6 * δ * (|c| + 3) with hw0
  have hδc' : δ ≤ 1 / c ^ 2 := by rw [le_div_iff₀ hc2]; linarith
  have hw0le : w0 ≤ 62 / 1000 := by
    have h1 : δ * |c| ≤ 1 / |c| := by
      rw [le_div_iff₀ hc0]
      have : δ * |c| * |c| = δ * c ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
      linarith
    have h2 : δ * 3 ≤ 3 / c ^ 2 := by
      have := mul_le_mul_of_nonneg_right hδc' (by norm_num : (0 : ℝ) ≤ 3)
      calc δ * 3 ≤ 1 / c ^ 2 * 3 := this
        _ = 3 / c ^ 2 := by ring
    have h3 : 1 / |c| ≤ 1 / 100 := by
      rw [div_le_div_iff₀ hc0 (by norm_num)]; linarith
    have h4 : 3 / c ^ 2 ≤ 3 / 10000 := by
      have : (10000 : ℝ) ≤ c ^ 2 := by
        rw [← sq_abs]; nlinarith
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) this
    rw [hw0]
    nlinarith
  -- bounds on the slope function
  have hfz : ∀ z, |z| ≤ 1 → |f z - c| ≤ 2 := fun z hz => hf.sub_le hz
  have hflow : ∀ z, |z| ≤ 1 → |c| - 2 ≤ |f z| := by
    intro z hz
    have h := abs_sub_abs_le_abs_sub c (f z)
    rw [abs_sub_comm] at h
    linarith [hfz z hz]
  have hderiv : ∀ z, |z| ≤ 1 → |deriv f z| ≤ 2 := fun z hz => (hf.2 z (abs_le.mp hz)).2.1
  -- the function and its derivative
  set B := v 0 / v 2 - v' 0 / v' 2 with hBdef
  set E := v 1 / v 2 - v' 1 / v' 2 with hEdef
  set a0 : ℝ → ℝ := fun z => lineAt x v z 0 - lineAt x' v' z 0 with ha0
  set a1 : ℝ → ℝ := fun z => lineAt x v z 1 - lineAt x' v' z 1 with ha1
  set h : ℝ → ℝ := fun z => a0 z + f z * a1 z with hh
  have hctr : ∀ z, ctr f x v z - ctr f x' v' z = h z := fun z => ctr_sub_eq f x v x' v' z
  have ha0d : ∀ z, HasDerivAt a0 B z := fun z =>
    (hasDerivAt_lineAt x v 0 z).sub (hasDerivAt_lineAt x' v' 0 z)
  have ha1d : ∀ z, HasDerivAt a1 E z := fun z =>
    (hasDerivAt_lineAt x v 1 z).sub (hasDerivAt_lineAt x' v' 1 z)
  have hhd : ∀ z, HasDerivAt h (B + (deriv f z * a1 z + f z * E)) z := fun z =>
    (ha0d z).add ((hd z).hasDerivAt.mul (ha1d z))
  -- `a1` is affine
  have ha1aff : ∀ z, a1 z = a1 0 + E * z := by
    intro z
    simp only [ha1, lineAt_apply, hEdef]
    ring
  -- `|B| ≤ 4`
  have hBle : |B| ≤ 4 := by
    have hq : ∀ w : Space, ‖w‖ = 1 → (1 / 2 : ℝ) ≤ |w 2| → |w 0 / w 2| ≤ 2 := by
      intro w hw hw2
      have h0 : |w 0| ≤ 1 := (coord_abs_le w 0).trans hw.le
      have hw2' : 0 < |w 2| := by linarith
      rw [abs_div, div_le_iff₀ hw2']
      linarith
    calc |B| ≤ |v 0 / v 2| + |v' 0 / v' 2| := abs_sub _ _
      _ ≤ 4 := by linarith [hq v hv hv2, hq v' hv' hv2']
  -- the slope identity
  have hSid : S = B / c + E := by
    rw [hSdef, slX_sub_eq hcne]
  -- main estimate on two heights
  have hdiam : ∀ z1 ∈ Z2 f δ x v x' v', ∀ z2 ∈ Z2 f δ x v x' v', z1 < z2 →
      z2 - z1 ≤ 18 * δ / |S| := by
    intro z1 hz1 z2 hz2 h12
    have hz1' : |z1| ≤ 1 := abs_le.mpr hz1.1
    have hz2' : |z2| ≤ 1 := abs_le.mpr hz2.1
    have hh1 : |h z1| ≤ w0 := by rw [← hctr]; exact hz1.2
    have hh2 : |h z2| ≤ w0 := by rw [← hctr]; exact hz2.2
    -- bound on `a1` at the two heights
    have ha0b : ∀ z, |z| ≤ 1 → |a0 z| ≤ 10 := by
      intro z hz
      have hL := norm_lineAt_le hδ hv hv2 hT hz
      have hL' := norm_lineAt_le hδ hv' hv2' hT' hz
      have h1 := coord_abs_le (lineAt x v z) 0
      have h2 := coord_abs_le (lineAt x' v' z) 0
      calc |a0 z| ≤ |lineAt x v z 0| + |lineAt x' v' z 0| := abs_sub _ _
        _ ≤ 10 := by linarith
    have ha1b : ∀ z, |z| ≤ 1 → |h z| ≤ w0 → |a1 z| ≤ (w0 + 10) / (|c| - 2) := by
      intro z hz hhz
      have hf0 : 0 < |c| - 2 := by linarith
      rw [le_div_iff₀ hf0]
      have hm := hflow z hz
      have heq : f z * a1 z = h z - a0 z := by simp only [hh]; ring
      have h1 : |f z * a1 z| ≤ w0 + 10 := by
        rw [heq]
        exact (abs_sub _ _).trans (by linarith [ha0b z hz])
      rw [abs_mul] at h1
      calc |a1 z| * (|c| - 2) ≤ |a1 z| * |f z| := by
            exact mul_le_mul_of_nonneg_left hm (abs_nonneg _)
        _ = |f z| * |a1 z| := by ring
        _ ≤ w0 + 10 := h1
    -- mean value theorem
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope h
      (fun z => B + (deriv f z * a1 z + f z * E)) h12
      (fun z _ => (hhd z).continuousAt.continuousWithinAt)
      (fun z _ => hhd z)
    have hξ1 : |ξ| ≤ 1 := abs_le.mpr ⟨by linarith [hz1.1.1, hξ.1], by linarith [hz2.1.2, hξ.2]⟩
    -- `|a1 ξ|`
    have ha1ξ : |a1 ξ| ≤ (w0 + 10) / (|c| - 2) := by
      have hmax := abs_affine_le_max (α := a1 0) (E := E) hξ.1.le hξ.2.le
      rw [← ha1aff, ← ha1aff, ← ha1aff] at hmax
      exact hmax.trans (max_le (ha1b z1 hz1' hh1) (ha1b z2 hz2' hh2))
    -- the derivative at `ξ`
    set D := B + (deriv f ξ * a1 ξ + f ξ * E) with hDdef
    have hDeq : D = f ξ * S - B * (f ξ - c) / c + deriv f ξ * a1 ξ := by
      rw [hDdef, hSid]
      field_simp
      ring
    have hcS : 100 ≤ c ^ 2 * |S| := by
      rw [div_le_iff₀ hc2] at hB; linarith
    have herr : |B * (f ξ - c) / c| + |deriv f ξ * a1 ξ| ≤ 286 / 1000 * |c| * |S| :=
      far_err_arith hc hBle (hfz ξ hξ1) (hderiv ξ hξ1) ha1ξ hw0le hcS
    have hrev : |f ξ * S| ≤ |D| + (|B * (f ξ - c) / c| + |deriv f ξ * a1 ξ|) := by
      have : f ξ * S = D + B * (f ξ - c) / c - deriv f ξ * a1 ξ := by rw [hDeq]; ring
      rw [this]
      calc |D + B * (f ξ - c) / c - deriv f ξ * a1 ξ|
          ≤ |D + B * (f ξ - c) / c| + |deriv f ξ * a1 ξ| := abs_sub _ _
        _ ≤ |D| + |B * (f ξ - c) / c| + |deriv f ξ * a1 ξ| := by
            gcongr
            exact abs_add_le _ _
        _ = |D| + (|B * (f ξ - c) / c| + |deriv f ξ * a1 ξ|) := by ring
    have hDlow : 69 / 100 * |c| * |S| ≤ |D| := far_low_arith hc (hflow ξ hξ1) hrev herr
    -- conclude
    have hslope : |h z2 - h z1| = |D| * (z2 - z1) := by
      have hpos : 0 < z2 - z1 := by linarith
      rw [hξeq, abs_div, abs_of_pos hpos, div_mul_cancel₀ _ hpos.ne']
    have hdiff : |h z2 - h z1| ≤ 2 * w0 := (abs_sub _ _).trans (by linarith)
    have hw0' : 2 * w0 ≤ 124 / 10 * δ * |c| := by
      rw [hw0]
      have : (3 : ℝ) ≤ 3 / 100 * |c| := by linarith
      nlinarith
    have hpos : 0 < z2 - z1 := by linarith
    rw [le_div_iff₀ hS0]
    have hkey : 69 / 100 * |c| * |S| * (z2 - z1) ≤ 124 / 10 * δ * |c| := by
      calc 69 / 100 * |c| * |S| * (z2 - z1) ≤ |D| * (z2 - z1) :=
            mul_le_mul_of_nonneg_right hDlow hpos.le
        _ = |h z2 - h z1| := hslope.symm
        _ ≤ 124 / 10 * δ * |c| := hdiff.trans hw0'
    have h3 : |c| * (69 / 100 * (|S| * (z2 - z1))) ≤ |c| * (124 / 10 * δ) := by
      calc |c| * (69 / 100 * (|S| * (z2 - z1))) = 69 / 100 * |c| * |S| * (z2 - z1) := by ring
        _ ≤ 124 / 10 * δ * |c| := hkey
        _ = |c| * (124 / 10 * δ) := by ring
    have h4 := le_of_mul_le_mul_left h3 hc0
    have h5 : (z2 - z1) * |S| ≤ 124 / 10 * δ / (69 / 100) := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    calc (z2 - z1) * |S| ≤ 124 / 10 * δ / (69 / 100) := h5
      _ ≤ 18 * δ := by rw [div_le_iff₀ (by norm_num)]; nlinarith
  -- volume by diameter
  refine (Real.volume_le_diam _).trans (Metric.ediam_le fun z1 hz1 z2 hz2 => ?_)
  rw [edist_dist, Real.dist_eq]
  apply ENNReal.ofReal_le_ofReal
  rcases lt_trichotomy z1 z2 with h12 | h12 | h12
  · rw [abs_sub_comm, abs_of_pos (by linarith)]
    exact hdiam z1 hz1 z2 hz2 h12
  · subst h12; simp only [sub_self, abs_zero]; positivity
  · rw [abs_of_pos (by linarith)]
    exact hdiam z2 hz2 z1 hz1 h12

end WangZahlLot.Obl.wz_intermediate_twist_normalization
