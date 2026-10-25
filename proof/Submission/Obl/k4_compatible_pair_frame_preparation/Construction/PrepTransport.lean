-- Adapted from this LOT tree, o206, session x0753, commit f0f3bdbb,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/PrepTransport.lean.
-- Earlier attribution comments are retained below.

-- Adapted from this LOT tree, o104, session x0472, commit 1aecc7d,
-- Submission/Obl/k4_terminal_time_extension/PrepTransport.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.PrepInterface
import Submission.Lib.K4ChartLifting.PolyAlgebra

/-!
# Old tests in the base coordinates of a frame

A frame `(T, j, c, u, Q)` with scale `100 κ` has base coordinates
`z = ((2^T t - j - 1/2) / (100 κ), Q⁻¹ (y - c - t u) / (100 κ))`; with the normalized hidden
coordinate `w = B x₃` the physical point `x = (t, y₁, y₂, x₃)` is an affine function of
`(z, w)` (`physVar`).  An old test `R` becomes `transport R = R ∘ physVar`, of the same
total degree, with `transport R (base l t, B x₃(l,t)) = R (x l t)` and
`∂_w transport R = B⁻¹ transport (∂₃ R)`.  The chain rule and the coefficient bounds
come from the accepted lib `K4ChartLifting.PolyAlgebra`.
-/

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction

open MvPolynomial Submission.Lib.K4ChartLifting

/-- The physical time of the frame as a polynomial of the base coordinates. -/
noncomputable def physTime (T : ℕ) (j κ : ℝ) : MvPolynomial (Fin 4) ℝ :=
  C ((j + 1 / 2) / (2 : ℝ) ^ T) + C (100 * κ / (2 : ℝ) ^ T) * X 0

/-- The physical coordinates `x` as affine polynomials of `(z, w)`. -/
noncomputable def physVar (T : ℕ) (j κ B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![physTime T j κ,
    C (c 0) + C (u 0) * physTime T j κ + C (100 * κ * Q 0 0) * X 1 + C (100 * κ * Q 0 1) * X 2,
    C (c 1) + C (u 1) * physTime T j κ + C (100 * κ * Q 1 0) * X 1 + C (100 * κ * Q 1 1) * X 2,
    C B⁻¹ * X 3]

/-- An old test in the base coordinates of a frame. -/
noncomputable def transport (T : ℕ) (j κ B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (R : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  bind₁ (physVar T j κ B c u Q) R

/-- The point `(base l t, B x₃(l,t))`. -/
noncomputable def basePt (T : ℕ) (j κ B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) : Fin 4 → ℝ :=
  Fin.snoc (fun i : Fin 3 => base T j κ c u Q l t i) (B * (x l t) 3)

theorem toEuclideanLin_inv_cancel {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (w : EuclideanSpace ℝ (Fin 2)) :
    Matrix.toEuclideanLin Q (Matrix.toEuclideanLin Q⁻¹ w) = w := by
  rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
    Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ)]
  simp

theorem eval_physVar {T : ℕ} {j κ B : ℝ} (hκ : κ ≠ 0) (hB : B ≠ 0)
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    (fun i => eval (basePt T j κ B c u Q l t) (physVar T j κ B c u Q i)) = x l t := by
  have hpow : (2 : ℝ) ^ T ≠ 0 := by positivity
  set g := Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u) with hg
  have hQg := toEuclideanLin_inv_cancel hQ (y l t - c - t • u)
  rw [← hg] at hQg
  have hQg0 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hQg
  have hQg1 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hQg
  simp only [Matrix.toLpLin_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hQg0 hQg1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hQg0 hQg1
  have hy0 : (y l t) 0 = (x l t) 1 := by simp [y]
  have hy1 : (y l t) 1 = (x l t) 2 := by simp [y]
  have hz0 : basePt T j κ B c u Q l t 0 = ((2 : ℝ) ^ T * t - j - 1 / 2) / (100 * κ) := by
    simp only [basePt]
    rw [show (0 : Fin 4) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
    simp [base]
  have hz1 : basePt T j κ B c u Q l t 1 = g 0 / (100 * κ) := by
    simp only [basePt]
    rw [show (1 : Fin 4) = Fin.castSucc 1 from rfl, Fin.snoc_castSucc]
    simp [base, hg]
  have hz2 : basePt T j κ B c u Q l t 2 = g 1 / (100 * κ) := by
    simp only [basePt]
    rw [show (2 : Fin 4) = Fin.castSucc 2 from rfl, Fin.snoc_castSucc]
    simp [base, hg]
  have hz3 : basePt T j κ B c u Q l t 3 = B * (x l t) 3 := by
    simp only [basePt]
    rw [show (3 : Fin 4) = Fin.last 3 from rfl, Fin.snoc_last]
  have htime : eval (basePt T j κ B c u Q l t) (physTime T j κ) = t := by
    simp only [physTime, map_add, map_mul, eval_C, eval_X]
    rw [hz0]
    field_simp
    ring
  have e0 : eval (basePt T j κ B c u Q l t) (physVar T j κ B c u Q 0) = x l t 0 := by
    change eval (basePt T j κ B c u Q l t) (physTime T j κ) = _
    rw [htime]; simp [x]
  have e1 : eval (basePt T j κ B c u Q l t) (physVar T j κ B c u Q 1) = x l t 1 := by
    change eval (basePt T j κ B c u Q l t) (C (c 0) + C (u 0) * physTime T j κ +
      C (100 * κ * Q 0 0) * X 1 + C (100 * κ * Q 0 1) * X 2) = _
    simp only [map_add, map_mul, eval_C, eval_X, htime]
    rw [hz1, hz2]
    have e : (x l t) 1 = c 0 + u 0 * t + (Q 0 0 * g 0 + Q 0 1 * g 1) := by
      rw [hQg0, ← hy0]; ring
    rw [e]
    field_simp
    ring
  have e2 : eval (basePt T j κ B c u Q l t) (physVar T j κ B c u Q 2) = x l t 2 := by
    change eval (basePt T j κ B c u Q l t) (C (c 1) + C (u 1) * physTime T j κ +
      C (100 * κ * Q 1 0) * X 1 + C (100 * κ * Q 1 1) * X 2) = _
    simp only [map_add, map_mul, eval_C, eval_X, htime]
    rw [hz1, hz2]
    have e : (x l t) 2 = c 1 + u 1 * t + (Q 1 0 * g 0 + Q 1 1 * g 1) := by
      rw [hQg1, ← hy1]; ring
    rw [e]
    field_simp
    ring
  have e3 : eval (basePt T j κ B c u Q l t) (physVar T j κ B c u Q 3) = x l t 3 := by
    change eval (basePt T j κ B c u Q l t) (C B⁻¹ * X 3) = _
    simp only [map_mul, eval_C, eval_X]
    rw [hz3]
    field_simp
  funext i
  fin_cases i
  exacts [e0, e1, e2, e3]

/-- The transported test at the base point of a trajectory is the old test. -/
theorem eval_transport {T : ℕ} {j κ B : ℝ} (hκ : κ ≠ 0) (hB : B ≠ 0)
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (R : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    eval (basePt T j κ B c u Q l t) (transport T j κ B c u Q R) = eval (x l t) R := by
  unfold transport
  have h := eval₂Hom_bind₁ (RingHom.id ℝ) (basePt T j κ B c u Q l t) (physVar T j κ B c u Q) R
  change eval₂Hom (RingHom.id ℝ) _ (bind₁ _ R) = eval₂Hom (RingHom.id ℝ) _ R
  rw [h]
  have e := eval_physVar (T := T) (j := j) (c := c) (u := u) hκ hB hQ l t
  change eval (fun i => eval (basePt T j κ B c u Q l t) (physVar T j κ B c u Q i)) R =
    eval (x l t) R
  rw [e]

theorem pderiv_physVar_three (T : ℕ) (j κ B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 4) :
    pderiv 3 (physVar T j κ B c u Q i) = if i = 3 then C B⁻¹ else 0 := by
  fin_cases i <;> simp [physVar, physTime, pderiv_X]

/-- The hidden derivative of a transported test. -/
theorem pderiv_transport (T : ℕ) (j κ B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (R : MvPolynomial (Fin 4) ℝ) :
    pderiv 3 (transport T j κ B c u Q R) = C B⁻¹ * transport T j κ B c u Q (pderiv 3 R) := by
  unfold transport
  rw [pderiv_bind₁, Finset.sum_eq_single (3 : Fin 4)]
  · rw [pderiv_physVar_three, ite_eq_left_iff.mpr (fun h => absurd rfl h), mul_comm]
  · intro b _ hb
    rw [pderiv_physVar_three, if_neg hb, mul_zero]
  · simp

theorem eval_pderiv_transport {T : ℕ} {j κ B : ℝ} (hκ : κ ≠ 0) (hB : B ≠ 0)
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (R : MvPolynomial (Fin 4) ℝ) (l : ℕ × (Fin 6 → ℝ)) (t : ℝ) :
    eval (basePt T j κ B c u Q l t) (pderiv 3 (transport T j κ B c u Q R)) =
      B⁻¹ * eval (x l t) (pderiv 3 R) := by
  rw [pderiv_transport, map_mul, eval_C, eval_transport hκ hB hQ]

theorem totalDegree_physVar_le (T : ℕ) (j κ B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 4) : (physVar T j κ B c u Q i).totalDegree ≤ 1 := by
  have hX (k : Fin 4) (a : ℝ) : (C a * X k : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 :=
    (totalDegree_mul _ _).trans (by simp [totalDegree_X])
  have htm : (physTime T j κ).totalDegree ≤ 1 := by
    unfold physTime
    exact (totalDegree_add _ _).trans (max_le (by simp) (hX 0 _))
  have hCt (a : ℝ) : (C a * physTime T j κ).totalDegree ≤ 1 :=
    (totalDegree_mul _ _).trans (by simpa using htm)
  fin_cases i
  · simpa [physVar] using htm
  · simp only [physVar, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le
      ((totalDegree_add _ _).trans (max_le (by simp) (hCt _))) (hX _ _))) (hX _ _))
  · simp only [physVar, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.tail_cons, Matrix.head_cons]
    refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le
      ((totalDegree_add _ _).trans (max_le (by simp) (hCt _))) (hX _ _))) (hX _ _))
  · simp only [physVar, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val_three, Matrix.cons_val_two,
      Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.tail_cons, Matrix.head_cons]
    exact hX _ _

theorem totalDegree_transport_le (T : ℕ) (j κ B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (R : MvPolynomial (Fin 4) ℝ) :
    (transport T j κ B c u Q R).totalDegree ≤ R.totalDegree :=
  totalDegree_bind₁_le_of_le_one _ (totalDegree_physVar_le T j κ B c u Q) R

/-- A common `ℓ¹` bound for the substituted coordinates. -/
noncomputable def physScale (T : ℕ) (j κ B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  1 + (|(j + 1 / 2) / (2 : ℝ) ^ T| + |100 * κ / (2 : ℝ) ^ T|) * (1 + |u 0| + |u 1|) +
    |c 0| + |c 1| + |100 * κ| * (|Q 0 0| + |Q 0 1| + |Q 1 0| + |Q 1 1|) + |B⁻¹|

theorem coeffL1_physTime_le (T : ℕ) (j κ : ℝ) :
    coeffL1 (physTime T j κ) ≤ |(j + 1 / 2) / (2 : ℝ) ^ T| + |100 * κ / (2 : ℝ) ^ T| := by
  unfold physTime
  refine (coeffL1_add_le _ _).trans ?_
  rw [coeffL1_C]
  have := coeffL1_C_mul_le (100 * κ / (2 : ℝ) ^ T) (X 0 : MvPolynomial (Fin 4) ℝ)
  rw [coeffL1_X, mul_one] at this
  linarith

theorem coeffL1_physVar_le (T : ℕ) (j κ B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 4) :
    coeffL1 (physVar T j κ B c u Q i) ≤ physScale T j κ B c u Q := by
  have htm := coeffL1_physTime_le T j κ
  set a := |(j + 1 / 2) / (2 : ℝ) ^ T| + |100 * κ / (2 : ℝ) ^ T| with ha
  have ha0 : 0 ≤ a := by positivity
  have hCX (k : Fin 4) (b : ℝ) : coeffL1 (C b * X k : MvPolynomial (Fin 4) ℝ) ≤ |b| := by
    have := coeffL1_C_mul_le b (X k : MvPolynomial (Fin 4) ℝ)
    rwa [coeffL1_X, mul_one] at this
  have hCt (b : ℝ) : coeffL1 (C b * physTime T j κ) ≤ |b| * a :=
    (coeffL1_C_mul_le _ _).trans (mul_le_mul_of_nonneg_left htm (abs_nonneg _))
  have hQ : 0 ≤ |100 * κ| * (|Q 0 0| + |Q 0 1| + |Q 1 0| + |Q 1 1|) := by positivity
  have hu0 := abs_nonneg (u 0)
  have hu1 := abs_nonneg (u 1)
  have hc0 := abs_nonneg (c 0)
  have hc1 := abs_nonneg (c 1)
  have hB := abs_nonneg B⁻¹
  have hscale : physScale T j κ B c u Q =
      1 + a * (1 + |u 0| + |u 1|) + |c 0| + |c 1| +
        |100 * κ| * (|Q 0 0| + |Q 0 1| + |Q 1 0| + |Q 1 1|) + |B⁻¹| := rfl
  have hQabs (r s : Fin 2) : |100 * κ * Q r s| = |100 * κ| * |Q r s| := abs_mul _ _
  fin_cases i
  · simp only [physVar, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [hscale]; nlinarith
  · simp only [physVar, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    have h1 := coeffL1_add_le (C (c 0) + C (u 0) * physTime T j κ + C (100 * κ * Q 0 0) * X 1)
      (C (100 * κ * Q 0 1) * X 2)
    have h2 := coeffL1_add_le (C (c 0) + C (u 0) * physTime T j κ) (C (100 * κ * Q 0 0) * X 1)
    have h3 := coeffL1_add_le (C (c 0) : MvPolynomial (Fin 4) ℝ) (C (u 0) * physTime T j κ)
    rw [coeffL1_C] at h3
    have h4 := hCt (u 0)
    have h5 := hCX 1 (100 * κ * Q 0 0)
    have h6 := hCX 2 (100 * κ * Q 0 1)
    rw [hQabs] at h5 h6
    rw [hscale]
    have hQ' : |100 * κ| * |Q 0 0| + |100 * κ| * |Q 0 1| ≤
        |100 * κ| * (|Q 0 0| + |Q 0 1| + |Q 1 0| + |Q 1 1|) := by
      have := abs_nonneg (Q 1 0); have := abs_nonneg (Q 1 1)
      have := abs_nonneg (100 * κ)
      nlinarith
    nlinarith
  · simp only [physVar, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.tail_cons, Matrix.head_cons]
    have h1 := coeffL1_add_le (C (c 1) + C (u 1) * physTime T j κ + C (100 * κ * Q 1 0) * X 1)
      (C (100 * κ * Q 1 1) * X 2)
    have h2 := coeffL1_add_le (C (c 1) + C (u 1) * physTime T j κ) (C (100 * κ * Q 1 0) * X 1)
    have h3 := coeffL1_add_le (C (c 1) : MvPolynomial (Fin 4) ℝ) (C (u 1) * physTime T j κ)
    rw [coeffL1_C] at h3
    have h4 := hCt (u 1)
    have h5 := hCX 1 (100 * κ * Q 1 0)
    have h6 := hCX 2 (100 * κ * Q 1 1)
    rw [hQabs] at h5 h6
    rw [hscale]
    have hQ' : |100 * κ| * |Q 1 0| + |100 * κ| * |Q 1 1| ≤
        |100 * κ| * (|Q 0 0| + |Q 0 1| + |Q 1 0| + |Q 1 1|) := by
      have := abs_nonneg (Q 0 0); have := abs_nonneg (Q 0 1)
      have := abs_nonneg (100 * κ)
      nlinarith
    nlinarith
  · simp only [physVar, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_three, Matrix.cons_val_two,
      Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.tail_cons, Matrix.head_cons]
    have := hCX 3 B⁻¹
    rw [hscale]; nlinarith

theorem one_le_physScale (T : ℕ) (j κ B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : 1 ≤ physScale T j κ B c u Q := by
  unfold physScale
  have : 0 ≤ (|(j + 1 / 2) / (2 : ℝ) ^ T| + |100 * κ / (2 : ℝ) ^ T|) * (1 + |u 0| + |u 1|) := by
    positivity
  have := abs_nonneg (c 0); have := abs_nonneg (c 1); have := abs_nonneg B⁻¹
  have : 0 ≤ |100 * κ| * (|Q 0 0| + |Q 0 1| + |Q 1 0| + |Q 1 1|) := by positivity
  linarith

/-- Coefficients of a transported test of degree at most two. -/
theorem abs_coeff_transport_le (T : ℕ) (j κ B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2)
    {A : ℝ} (hA : ∀ m, |R.coeff m| ≤ A) (m : Fin 4 →₀ ℕ) :
    |(transport T j κ B c u Q R).coeff m| ≤ 81 * A * physScale T j κ B c u Q ^ 2 := by
  have hS := one_le_physScale T j κ B c u Q
  have h1 := abs_coeff_le_coeffL1 (transport T j κ B c u Q R) m
  have h2 := coeffL1_bind₁_le (physVar T j κ B c u Q) _ hS (coeffL1_physVar_le T j κ B c u Q) R
  have h3 := coeffL1_le_of_coeff_le R hR A hA
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hpow : physScale T j κ B c u Q ^ R.totalDegree ≤ physScale T j κ B c u Q ^ 2 :=
    pow_le_pow_right₀ hS hR
  have hL1 := coeffL1_nonneg R
  norm_num at h3
  calc |(transport T j κ B c u Q R).coeff m| ≤ coeffL1 (transport T j κ B c u Q R) := h1
    _ ≤ coeffL1 R * physScale T j κ B c u Q ^ R.totalDegree := h2
    _ ≤ (81 * A) * physScale T j κ B c u Q ^ 2 := by
        apply mul_le_mul h3 hpow (by positivity) (by positivity)
    _ = 81 * A * physScale T j κ B c u Q ^ 2 := by ring

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction
