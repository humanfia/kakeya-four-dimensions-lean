/-
Adapted from: here:o116

Original heavy-strip packing and frame proofs by session x0644.
-/

import Submission.Lib.K4XInterface.Charts

/-! Separated affine strips have small intersections under an angular ball cap.
The estimates use separation modulo the simultaneous sign of normal and offset. -/

noncomputable section

namespace Submission.Lib.K4VelocityStrips

open Set MeasureTheory
open scoped RealInnerProductSpace

abbrev StripSpace := EuclideanSpace ℝ (Fin 2)

def affineStrip (n : StripSpace) (b r : ℝ) : Set StripSpace :=
  {x | |inner ℝ x n - b| ≤ r}

def stripWedge (n m : StripSpace) : ℝ := n 0 * m 1 - n 1 * m 0

theorem measurableSet_affineStrip (n : StripSpace) (b r : ℝ) :
    MeasurableSet (affineStrip n b r) :=
  (isClosed_le (by fun_prop) continuous_const).measurableSet

private theorem strip_inner (x y : StripSpace) :
    inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

private theorem strip_points_sub {n x y : StripSpace} {b r : ℝ}
    (hx : x ∈ affineStrip n b r) (hy : y ∈ affineStrip n b r) :
    |inner ℝ (x - y) n| ≤ 2 * r := by
  change |inner ℝ x n - b| ≤ r at hx
  change |inner ℝ y n - b| ≤ r at hy
  have hid : inner ℝ (x - y) n = (inner ℝ x n - b) - (inner ℝ y n - b) := by
    rw [inner_sub_left]
    ring
  rw [hid]
  exact (abs_sub _ _).trans (by linarith [hx, hy])

/-- Two strips with transverse normals have small diameter, for any underlying
law; no absolute continuity of the velocity palette is required. -/
theorem strip_intersection_diameter {n m x y : StripSpace} {b c r d : ℝ}
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hd : 0 < d)
    (hdet : d ≤ |stripWedge n m|)
    (hxn : x ∈ affineStrip n b r) (hxm : x ∈ affineStrip m c r)
    (hyn : y ∈ affineStrip n b r) (hym : y ∈ affineStrip m c r) :
    dist x y ≤ 8 * r / d := by
  let z := x - y
  have hr : 0 ≤ r := (abs_nonneg _).trans hxn
  have hzn : |inner ℝ z n| ≤ 2 * r := strip_points_sub hxn hyn
  have hzm : |inner ℝ z m| ≤ 2 * r := strip_points_sub hxm hym
  have hc (u : StripSpace) (hu : ‖u‖ = 1) (i : Fin 2) : |u i| ≤ 1 := by
    simpa only [hu, Real.norm_eq_abs] using PiLp.norm_apply_le u i
  have h0 : |stripWedge n m * z 0| ≤ 4 * r := by
    have hid : stripWedge n m * z 0 = m 1 * inner ℝ z n - n 1 * inner ℝ z m := by
      simp only [stripWedge, strip_inner]
      ring
    rw [hid]
    calc
      _ ≤ |m 1| * |inner ℝ z n| + |n 1| * |inner ℝ z m| := by
        simpa only [abs_mul] using abs_sub (m 1 * inner ℝ z n) (n 1 * inner ℝ z m)
      _ ≤ 1 * (2 * r) + 1 * (2 * r) :=
        add_le_add (mul_le_mul (hc m hm 1) hzn (abs_nonneg _) (by norm_num))
          (mul_le_mul (hc n hn 1) hzm (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  have h1 : |stripWedge n m * z 1| ≤ 4 * r := by
    have hid : stripWedge n m * z 1 = n 0 * inner ℝ z m - m 0 * inner ℝ z n := by
      simp only [stripWedge, strip_inner]
      ring
    rw [hid]
    calc
      _ ≤ |n 0| * |inner ℝ z m| + |m 0| * |inner ℝ z n| := by
        simpa only [abs_mul] using abs_sub (n 0 * inner ℝ z m) (m 0 * inner ℝ z n)
      _ ≤ 1 * (2 * r) + 1 * (2 * r) :=
        add_le_add (mul_le_mul (hc n hn 0) hzm (abs_nonneg _) (by norm_num))
          (mul_le_mul (hc m hm 0) hzn (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  have hnorm : |stripWedge n m| * ‖z‖ ≤ 8 * r := by
    have h := Submission.Lib.K4XInterface.norm_le_of_rows
      (1 : Matrix (Fin 2) (Fin 2) ℝ) (stripWedge n m • z)
      (a := 4 * r) (b := 4 * r) (by simpa using h0) (by simpa using h1)
    simpa [norm_smul, Real.norm_eq_abs, show 4 * r + 4 * r = 8 * r by ring] using h
  rw [dist_eq_norm]
  exact (le_div_iff₀ hd).mpr <| by
    calc
      ‖x - y‖ * d ≤ |stripWedge n m| * ‖z‖ := by dsimp [z]; nlinarith [norm_nonneg z]
      _ ≤ 8 * r := hnorm

/-- For two unit normals with nonnegative inner product, their distance is
at most twice the absolute determinant. -/
theorem unit_normals_dist_le_wedge {n m : StripSpace} (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    (hnm : 0 ≤ inner ℝ n m) : ‖n - m‖ ≤ 2 * |stripWedge n m| := by
  have hsqn : n 0 ^ 2 + n 1 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq n
    simpa [Fin.sum_univ_two, hn] using h.symm
  have hsqm : m 0 ^ 2 + m 1 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq m
    simpa [Fin.sum_univ_two, hm] using h.symm
  have hsum : stripWedge n m ^ 2 + inner ℝ n m ^ 2 = 1 := by
    calc
      _ = (n 0 ^ 2 + n 1 ^ 2) * (m 0 ^ 2 + m 1 ^ 2) := by
        simp only [stripWedge, strip_inner]
        ring
      _ = 1 := by rw [hsqn, hsqm]; norm_num
  have hi : inner ℝ n m ≤ 1 := by
    have h := abs_real_inner_le_norm n m
    rw [hn, hm, one_mul] at h
    exact (le_abs_self _).trans h
  have hd := norm_sub_sq_real n m
  rw [hn, hm] at hd
  have hnonneg : 0 ≤ inner ℝ n m * (1 - inner ℝ n m) := mul_nonneg hnm (by linarith)
  nlinarith [norm_nonneg (n - m), abs_nonneg (stripWedge n m), sq_abs (stripWedge n m)]

/-- Parameter separation forces angle separation whenever the two thin strips
meet in the used velocity range. -/
theorem separated_strip_wedge_of_nonneg_inner {n m x : StripSpace} {b c r ρ T : ℝ}
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hnm : 0 ≤ inner ℝ n m)
    (hT : 0 ≤ T) (hx : ‖x‖ ≤ T) (_hρ : 0 < ρ) (hsmall : 4 * r ≤ ρ)
    (hsep : ρ ≤ ‖n - m‖ + |b - c|)
    (hxn : x ∈ affineStrip n b r) (hxm : x ∈ affineStrip m c r) :
    ρ / (4 * (1 + T)) ≤ |stripWedge n m| := by
  have hr : 0 ≤ r := (abs_nonneg _).trans hxn
  have hb : |b - c| ≤ 2 * r + T * ‖n - m‖ := by
    have hid : b - c = (b - inner ℝ x n) + inner ℝ x (n - m) + (inner ℝ x m - c) := by
      rw [inner_sub_right]
      ring
    rw [hid]
    calc
      _ ≤ |b - inner ℝ x n| + |inner ℝ x (n - m)| + |inner ℝ x m - c| := abs_add_three _ _ _
      _ ≤ r + T * ‖n - m‖ + r := by
        apply add_le_add _ hxm
        apply add_le_add _
          ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _)))
        simpa only [affineStrip, mem_ofPred_eq, abs_sub_comm] using hxn
      _ = _ := by ring
  have hdist := unit_normals_dist_le_wedge hn hm hnm
  apply (div_le_iff₀ (show 0 < 4 * (1 + T) by positivity)).mpr
  have hmul := mul_le_mul_of_nonneg_left hdist (show 0 ≤ 1 + T by positivity)
  nlinarith

/-- The angle bound is insensitive to the simultaneous sign of a strip's
normal and offset. This is the separation used for heavy-strip packing. -/
theorem separated_strip_wedge {n m x : StripSpace} {b c r ρ T : ℝ}
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hT : 0 ≤ T) (hx : ‖x‖ ≤ T)
    (hρ : 0 < ρ) (hsmall : 4 * r ≤ ρ)
    (hsep : ρ ≤ ‖n - m‖ + |b - c|) (hsep' : ρ ≤ ‖n + m‖ + |b + c|)
    (hxn : x ∈ affineStrip n b r) (hxm : x ∈ affineStrip m c r) :
    ρ / (4 * (1 + T)) ≤ |stripWedge n m| := by
  by_cases hi : 0 ≤ inner ℝ n m
  · exact separated_strip_wedge_of_nonneg_inner hn hm hi hT hx hρ hsmall hsep hxn hxm
  · have hxm' : x ∈ affineStrip (-m) (-c) r := by
      change |inner ℝ x (-m) - -c| ≤ r
      simpa only [affineStrip, mem_ofPred_eq, inner_neg_right, neg_sub_neg, abs_sub_comm] using hxm
    have h := separated_strip_wedge_of_nonneg_inner hn (by simpa using hm)
      (show 0 ≤ inner ℝ n (-m) by rw [inner_neg_right]; linarith) hT hx hρ hsmall
      (by simpa only [sub_neg_eq_add] using hsep') hxn hxm'
    have hid : stripWedge n (-m) = -stripWedge n m := by simp [stripWedge]; ring
    simpa only [hid, abs_neg] using h

/-- Moving the parameters of a strip by at most `ρ` enlarges its width only by
`(1 + T) * ρ` on velocities of norm at most `T`. -/
theorem affineStrip_mem_of_close_parameters {n m x : StripSpace} {b c r ρ T : ℝ}
    (hT : 0 ≤ T) (hx : ‖x‖ ≤ T)
    (hclose : ‖n - m‖ + |b - c| ≤ ρ) (hxn : x ∈ affineStrip n b r) :
    x ∈ affineStrip m c (r + (1 + T) * ρ) := by
  have hdist : ‖m - n‖ ≤ ρ := by rw [norm_sub_rev]; linarith [abs_nonneg (b - c)]
  have hoffset : |b - c| ≤ ρ := by linarith [norm_nonneg (n - m)]
  change |inner ℝ x m - c| ≤ _
  have hid : inner ℝ x m - c = (inner ℝ x n - b) + inner ℝ x (m - n) + (b - c) := by
    rw [inner_sub_right]
    ring
  rw [hid]
  calc
    _ ≤ |inner ℝ x n - b| + |inner ℝ x (m - n)| + |b - c| := abs_add_three _ _ _
    _ ≤ r + T * ρ + ρ := by
      apply add_le_add _ hoffset
      apply add_le_add hxn
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul hx hdist (norm_nonneg _) hT)
    _ = _ := by ring

theorem affineStrip_mem_of_close_parameters_mod_sign {n m x : StripSpace} {b c r ρ T : ℝ}
    (hT : 0 ≤ T) (hx : ‖x‖ ≤ T)
    (hclose : ‖n - m‖ + |b - c| ≤ ρ ∨ ‖n + m‖ + |b + c| ≤ ρ)
    (hxn : x ∈ affineStrip n b r) :
    x ∈ affineStrip m c (r + (1 + T) * ρ) := by
  rcases hclose with h | h
  · exact affineStrip_mem_of_close_parameters hT hx h hxn
  · have h' := affineStrip_mem_of_close_parameters (n := n) (m := -m)
      (b := b) (c := -c) hT hx (by simpa only [sub_neg_eq_add] using h) hxn
    change |inner ℝ x m - c| ≤ _
    simpa only [affineStrip, mem_ofPred_eq, inner_neg_right, neg_sub_neg, abs_sub_comm] using h'

end Submission.Lib.K4VelocityStrips
