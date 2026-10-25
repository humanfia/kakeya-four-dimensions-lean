/- Adapted from: here:o266
Original accepted finite kernel: here:o016, session x0049.
Original file: Submission/Obl/k4_scalar_coefficient_clustering/Geometry.lean.
The accepted scalar binning/lifting kernels are packaged here because
shared-library contributions cannot import obligation modules. -/
import Mathlib

namespace Submission.Lib.K4ScalarProfileAmplitude.Scalar

open scoped RealInnerProductSpace

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Coeff := EuclideanSpace ℝ (Fin 3)

def quadratic (a : Coeff) (t : ℝ) : ℝ := a 0 + t * a 1 + t ^ 2 * a 2

def liftBase (a : Coeff) (s : ℝ) : Plane := WithLp.toLp 2 ![a 0, s]

def liftSlope (a : Coeff) (s : ℝ) : Plane := WithLp.toLp 2 ![a 1 - s, a 2]

def liftTrace (a : Coeff) (s t : ℝ) : Plane := liftBase a s + t • liftSlope a s

theorem liftTrace_zero (a : Coeff) (s t : ℝ) :
    liftTrace a s t 0 = a 0 + t * (a 1 - s) := by
  simp [liftTrace, liftBase, liftSlope, PiLp.add_apply, PiLp.smul_apply]

theorem liftTrace_one (a : Coeff) (s t : ℝ) :
    liftTrace a s t 1 = s + t * a 2 := by
  simp [liftTrace, liftBase, liftSlope, PiLp.add_apply, PiLp.smul_apply]

/-- The auxiliary parameter disappears under the time-dependent scalar projection. -/
theorem liftTrace_scalar (a : Coeff) (s t : ℝ) :
    liftTrace a s t 0 + t * liftTrace a s t 1 = quadratic a t := by
  rw [liftTrace_zero, liftTrace_one, quadratic]
  ring

theorem plane_norm_le_abs_add (z : Plane) : ‖z‖ ≤ |z 0| + |z 1| := by
  have hsq : ‖z‖ ^ 2 = (z 0) ^ 2 + (z 1) ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  nlinarith [norm_nonneg z, abs_nonneg (z 0), abs_nonneg (z 1),
    sq_abs (z 0), sq_abs (z 1), mul_nonneg (abs_nonneg (z 0)) (abs_nonneg (z 1))]

theorem coeff_norm_le_abs_add (a : Coeff) : ‖a‖ ≤ |a 0| + |a 1| + |a 2| := by
  have hsq : ‖a‖ ^ 2 = (a 0) ^ 2 + (a 1) ^ 2 + (a 2) ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  nlinarith [norm_nonneg a, abs_nonneg (a 0), abs_nonneg (a 1), abs_nonneg (a 2),
    sq_abs (a 0), sq_abs (a 1), sq_abs (a 2),
    mul_nonneg (abs_nonneg (a 0)) (abs_nonneg (a 1)),
    mul_nonneg (abs_nonneg (a 0)) (abs_nonneg (a 2)),
    mul_nonneg (abs_nonneg (a 1)) (abs_nonneg (a 2))]

theorem lift_norm_bounds {a : Coeff} {B s : ℝ} (ha : ‖a‖ ≤ B)
    (hB : 1 ≤ B) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖liftBase a s‖ ≤ 2 * B ∧ ‖liftSlope a s‖ ≤ 3 * B := by
  have h0 : |a 0| ≤ B := (PiLp.norm_apply_le a 0).trans ha
  have h1 : |a 1| ≤ B := (PiLp.norm_apply_le a 1).trans ha
  have h2 : |a 2| ≤ B := (PiLp.norm_apply_le a 2).trans ha
  have hb := plane_norm_le_abs_add (liftBase a s)
  have hu := plane_norm_le_abs_add (liftSlope a s)
  simp only [liftBase, liftSlope, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at hb hu
  rw [abs_of_nonneg hs.1] at hb
  constructor
  · change ‖WithLp.toLp 2 ![a 0, s]‖ ≤ 2 * B
    linarith [hs.2]
  · change ‖WithLp.toLp 2 ![a 1 - s, a 2]‖ ≤ 3 * B
    have ht := abs_sub (a 1) s
    rw [abs_of_nonneg hs.1] at ht
    linarith [hs.2]

/-- Two orthogonal unit axes control the Euclidean norm in the plane. -/
theorem plane_norm_le_two_mul {e₁ e₂ z : Plane} {v : ℝ}
    (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (horth : inner ℝ e₁ e₂ = 0)
    (hz₁ : |inner ℝ z e₁| ≤ v) (hz₂ : |inner ℝ z e₂| ≤ v) : ‖z‖ ≤ 2 * v := by
  let e : Fin 2 → Plane := ![e₁, e₂]
  have hon : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [e, real_inner_self_eq_norm_sq, h₁]
    · simpa [e] using horth
    · simpa [e, real_inner_comm] using horth
    · simpa [e, real_inner_self_eq_norm_sq, h₂]
  let basis : OrthonormalBasis (Fin 2) ℝ Plane :=
    OrthonormalBasis.mk hon
      (hon.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge
  have he : ∀ i, basis i = e i := by
    intro i
    exact congrFun (OrthonormalBasis.coe_mk hon _) i
  have hsq := basis.sum_sq_inner_left z
  simp only [Fin.sum_univ_two, he, e, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at hsq
  have hv : 0 ≤ v := (abs_nonneg _).trans hz₁
  have hs₁ : (inner ℝ z e₁) ^ 2 ≤ v ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hv).mpr hz₁
  have hs₂ : (inner ℝ z e₂) ^ 2 ≤ v ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hv).mpr hz₂
  nlinarith [norm_nonneg z]

/-- The two endpoint differences already recover all three scalar coefficients. -/
theorem coefficient_dist_of_lift_endpoints {a b : Coeff} {s r L : ℝ}
    (hzero : ‖liftTrace a s 0 - liftTrace b r 0‖ ≤ L)
    (hone : ‖liftTrace a s 1 - liftTrace b r 1‖ ≤ L) : ‖a - b‖ ≤ 6 * L := by
  have h00 := (PiLp.norm_apply_le (liftTrace a s 0 - liftTrace b r 0) 0).trans hzero
  have h01 := (PiLp.norm_apply_le (liftTrace a s 0 - liftTrace b r 0) 1).trans hzero
  have h10 := (PiLp.norm_apply_le (liftTrace a s 1 - liftTrace b r 1) 0).trans hone
  have h11 := (PiLp.norm_apply_le (liftTrace a s 1 - liftTrace b r 1) 1).trans hone
  simp only [Real.norm_eq_abs, PiLp.sub_apply, liftTrace_zero, liftTrace_one,
    zero_mul, add_zero, one_mul] at h00 h01 h10 h11
  have h2 : |a 2 - b 2| ≤ 2 * L := by
    have h := abs_sub (s + a 2 - (r + b 2)) (s - r)
    have he : s + a 2 - (r + b 2) - (s - r) = a 2 - b 2 := by ring
    rw [he] at h
    linarith
  have h1 : |a 1 - b 1| ≤ 3 * L := by
    have h := abs_add_three (a 0 + (a 1 - s) - (b 0 + (b 1 - r)))
      (-(a 0 - b 0)) (s - r)
    have he : a 0 + (a 1 - s) - (b 0 + (b 1 - r)) + -(a 0 - b 0) + (s - r) =
        a 1 - b 1 := by ring
    rw [he, abs_neg] at h
    linarith
  have h := coeff_norm_le_abs_add (a - b)
  simp only [PiLp.sub_apply] at h
  linarith

/-- A unit narrow normal sees a fixed fraction of a dummy displacement at an endpoint. -/
theorem narrow_normal_endpoint {e : Plane} (he : ‖e‖ = 1) :
    (1 / 4 : ℝ) ≤ |e 1| ∨ (1 / 4 : ℝ) ≤ |e 1 - e 0| := by
  by_contra! h
  have hs : (e 0) ^ 2 + (e 1) ^ 2 = 1 := by
    have hh := EuclideanSpace.real_norm_sq_eq e
    rw [he] at hh
    simpa [Fin.sum_univ_two] using hh.symm
  have h0 : |e 0| < 1 / 2 := by
    have ht := abs_sub (e 1) (e 1 - e 0)
    simp only [sub_sub_cancel] at ht
    linarith
  nlinarith [sq_abs (e 0), sq_abs (e 1), abs_nonneg (e 0), abs_nonneg (e 1)]

def InNarrowPlank (c w e : Plane) (u : ℝ) (a : Coeff) (s : ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, |inner ℝ (liftTrace a s t - c - t • w) e| ≤ u

def InPlank (c w e₁ e₂ : Plane) (u v : ℝ) (a : Coeff) (s : ℝ) : Prop :=
  InNarrowPlank c w e₁ u a s ∧ InNarrowPlank c w e₂ v a s

theorem inner_lift_difference_le {c w e : Plane} {u : ℝ} {a b : Coeff} {s r t : ℝ}
    (ha : InNarrowPlank c w e u a s) (hb : InNarrowPlank c w e u b r)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |inner ℝ (liftTrace a s t - liftTrace b r t) e| ≤ 2 * u := by
  have heq : liftTrace a s t - liftTrace b r t =
      (liftTrace a s t - c - t • w) - (liftTrace b r t - c - t • w) := by module
  rw [heq, inner_sub_left]
  exact (abs_sub _ _).trans (by linarith [ha t ht, hb t ht])

theorem coefficient_dist_in_plank {c w e₁ e₂ : Plane} {u v : ℝ} {a b : Coeff} {s r : ℝ}
    (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (horth : inner ℝ e₁ e₂ = 0) (huv : u ≤ v)
    (ha : InPlank c w e₁ e₂ u v a s) (hb : InPlank c w e₁ e₂ u v b r) :
    ‖a - b‖ ≤ 24 * v := by
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖liftTrace a s t - liftTrace b r t‖ ≤ 4 * v := by
    intro t ht
    have hn := inner_lift_difference_le ha.1 hb.1 ht
    have hw := inner_lift_difference_le ha.2 hb.2 ht
    have hn' : |inner ℝ (liftTrace a s t - liftTrace b r t) e₁| ≤ 2 * v := by
      linarith
    have := plane_norm_le_two_mul h₁ h₂ horth hn' hw
    linarith
  have := coefficient_dist_of_lift_endpoints (hd 0 (by norm_num)) (hd 1 (by norm_num))
  linarith

theorem dummy_gap_in_plank {c w e : Plane} {u : ℝ} {a : Coeff} {s r : ℝ}
    (he : ‖e‖ = 1) (hs : InNarrowPlank c w e u a s)
    (hr : InNarrowPlank c w e u a r) : |s - r| ≤ 8 * u := by
  have hzero := inner_lift_difference_le hs hr (t := 0) (by norm_num)
  have hone := inner_lift_difference_le hs hr (t := 1) (by norm_num)
  have hz : inner ℝ (liftTrace a s 0 - liftTrace a r 0) e = (s - r) * e 1 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, PiLp.sub_apply, liftTrace_zero, liftTrace_one]
    ring
  have ho : inner ℝ (liftTrace a s 1 - liftTrace a r 1) e =
      (s - r) * (e 1 - e 0) := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, PiLp.sub_apply, liftTrace_zero, liftTrace_one]
    ring
  rw [hz, abs_mul] at hzero
  rw [ho, abs_mul] at hone
  rcases narrow_normal_endpoint he with h | h
  · have hm := mul_le_mul_of_nonneg_left h (abs_nonneg (s - r))
    linarith
  · have hm := mul_le_mul_of_nonneg_left h (abs_nonneg (s - r))
    linarith

end
end Submission.Lib.K4ScalarProfileAmplitude.Scalar
