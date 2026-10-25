import Mathlib

/-!
# Quadratic tests in the hidden coordinate

The chart tests of the frozen `chart` predicate are polynomials `R : MvPolynomial (Fin 4) ℝ`
of total degree at most two, controlled through `eval R`, `eval (pderiv 3 R)` and
`eval (pderiv 3 (pderiv 3 R))` along trajectories.  This module records, for any coordinate
`i` (the hidden coordinate is `i = 3`):

* `eval_update_add`: the exact Taylor expansion
  `R(v + s eᵢ) = R(v) + s ∂ᵢR(v) + s²/2 ∂ᵢ²R`, with `∂ᵢ²R` constant
  (`eval_pderiv_pderiv_eq`) and `∂ᵢ³R = 0`; `eval_update_add_pderiv`: `∂ᵢR` is affine in the
  coordinate;
* `quadratic_nearest_root` / `exists_nearest_root_update`: the paper's nearest-root identity
  (`tex-03-comparison.tex`, display `a02:nearest-quadratic-root`, used in Lemma 3.5,
  Prop. 4.11 and Prop. 6.8): if `∂ᵢR(v) = q ≠ 0` and `2 |∂ᵢ²R · R(v)| ≤ q²/2`, the zero of
  `R` on the coordinate line on which `∂ᵢR` keeps the sign of `q` lies within
  `2 |R(v)| / |q|` of `v`, and there `|∂ᵢR| = √(q² - 2 ∂ᵢ²R R(v))`.

Adapted from: here:o007 — the univariate slice `coordPoly` and the lemmas `eval_coordPoly`,
`derivative_coordPoly`, `natDegree_coordPoly_le`, `totalDegree_pderiv_le_pred` follow
`coordinatePolynomialHom`, `eval_coordinatePolynomialHom`, `derivative_coordinatePolynomialHom`,
`natDegree_eval₂_affine_le` and `totalDegree_pderiv_le` of this tree's obligation o007
(`Submission/Obl/k4_quadratic_slope_volume/PolynomialSlices.lean`). The Taylor expansion and
the nearest-root statements are new here.
-/

namespace Submission.Lib.K4HiddenQuadratic

open Polynomial

noncomputable section


/-- Exact second-order Taylor expansion of a univariate polynomial of degree at most two. -/
theorem eval_add_of_natDegree_le_two (p : ℝ[X]) (hp : p.natDegree ≤ 2) (a s : ℝ) :
    p.eval (a + s) = p.eval a + s * p.derivative.eval a +
      s ^ 2 / 2 * p.derivative.derivative.eval a := by
  have hp' : p = C (p.coeff 0) + C (p.coeff 1) * X + C (p.coeff 2) * X ^ 2 := by
    have h := p.as_sum_range' 3 (by omega)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at h
    rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial] at h
    simpa using h
  set c0 := p.coeff 0
  set c1 := p.coeff 1
  set c2 := p.coeff 2
  rw [hp']
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, derivative_add, derivative_mul,
    derivative_C, derivative_X, derivative_X_pow, zero_mul, zero_add, mul_one]
  push_cast
  ring

variable {σ : Type*}

/-- The slice of `R` through `v` along coordinate `i`, as a univariate polynomial. -/
noncomputable def coordPoly [DecidableEq σ] (v : σ → ℝ) (i : σ) (R : MvPolynomial σ ℝ) : ℝ[X] :=
  MvPolynomial.eval₂ C (fun j => if j = i then X else C (v j)) R

/-- The slice polynomial evaluates to `R` on the coordinate line. -/
theorem eval_coordPoly [DecidableEq σ] (v : σ → ℝ) (i : σ) (R : MvPolynomial σ ℝ) (w : ℝ) :
    (coordPoly v i R).eval w = MvPolynomial.eval (Function.update v i w) R := by
  induction R using MvPolynomial.induction_on with
  | C a => simp [coordPoly]
  | add P Q hP hQ =>
    simp only [coordPoly, MvPolynomial.eval₂_add, eval_add, map_add] at *; rw [hP, hQ]
  | mul_X P j hP =>
    simp only [coordPoly, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, eval_mul, map_mul,
      MvPolynomial.eval_X] at *
    rw [hP]
    congr 1
    by_cases h : j = i
    · subst h; simp
    · simp [h]

/-- Differentiating the slice is taking the partial derivative. -/
theorem derivative_coordPoly [DecidableEq σ] (v : σ → ℝ) (i : σ) (R : MvPolynomial σ ℝ) :
    (coordPoly v i R).derivative = coordPoly v i (MvPolynomial.pderiv i R) := by
  induction R using MvPolynomial.induction_on with
  | C a => simp [coordPoly]
  | add P Q hP hQ =>
    simp only [coordPoly, MvPolynomial.eval₂_add, map_add] at *; rw [hP, hQ]
  | mul_X P j hP =>
    simp only [coordPoly] at hP ⊢
    by_cases h : j = i
    · subst h
      simp [MvPolynomial.eval₂_mul, derivative_mul, hP, MvPolynomial.pderiv_X, mul_comm]
    · simp [MvPolynomial.eval₂_mul, derivative_mul, hP, h, MvPolynomial.pderiv_X, mul_comm]

/-- The slice has degree at most the total degree. -/
theorem natDegree_coordPoly_le [DecidableEq σ] (v : σ → ℝ) (i : σ) (R : MvPolynomial σ ℝ) :
    (coordPoly v i R).natDegree ≤ R.totalDegree := by
  conv_lhs => rw [coordPoly, R.as_sum]
  rw [MvPolynomial.eval₂_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [MvPolynomial.eval₂_monomial]
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  calc (m.prod fun j e => (if j = i then X else C (v j)) ^ e).natDegree
      ≤ m.sum (fun j e => ((if j = i then X else C (v j)) ^ e).natDegree) :=
        Polynomial.natDegree_prod_le _ _
    _ ≤ m.sum (fun _ e => e) := by
      apply Finsupp.sum_le_sum
      intro j _
      apply Polynomial.natDegree_pow_le.trans
      split_ifs <;> simp
    _ ≤ R.totalDegree := MvPolynomial.le_totalDegree hm

/-- A partial derivative lowers the total degree by at least one. -/
theorem totalDegree_pderiv_le_pred (R : MvPolynomial σ ℝ) (i : σ) :
    (MvPolynomial.pderiv i R).totalDegree ≤ R.totalDegree - 1 := by
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro m hm
  have hmne : (MvPolynomial.pderiv i R).coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hcoeff : R.coeff (m + Finsupp.single i 1) ≠ 0 := by
    rw [MvPolynomial.coeff_pderiv] at hmne
    exact (mul_ne_zero_iff.mp hmne).1
  have hdeg := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hcoeff)
  have hsum : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (by simp) (by intros; rfl)]
    simp
  rw [hsum] at hdeg
  omega

/-- The second hidden derivative of a test of total degree at most two is a constant. -/
theorem pderiv_pderiv_eq_C (R : MvPolynomial σ ℝ) (hR : R.totalDegree ≤ 2) (i : σ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv i R) =
      MvPolynomial.C ((MvPolynomial.pderiv i (MvPolynomial.pderiv i R)).coeff 0) := by
  apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
  have h1 := totalDegree_pderiv_le_pred R i
  have h2 := totalDegree_pderiv_le_pred (MvPolynomial.pderiv i R) i
  omega

/-- The second hidden derivative of a test of total degree at most two does not depend on
the point. -/
theorem eval_pderiv_pderiv_eq (R : MvPolynomial σ ℝ) (hR : R.totalDegree ≤ 2) (i : σ)
    (v v' : σ → ℝ) :
    MvPolynomial.eval v (MvPolynomial.pderiv i (MvPolynomial.pderiv i R)) =
      MvPolynomial.eval v' (MvPolynomial.pderiv i (MvPolynomial.pderiv i R)) := by
  rw [pderiv_pderiv_eq_C R hR i]
  simp

/-- The third hidden derivative of a test of total degree at most two vanishes. -/
theorem pderiv_pderiv_pderiv_eq_zero (R : MvPolynomial σ ℝ) (hR : R.totalDegree ≤ 2) (i : σ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv i (MvPolynomial.pderiv i R)) = 0 := by
  rw [pderiv_pderiv_eq_C R hR i, MvPolynomial.pderiv_C]

/-- **Exact Taylor expansion in one coordinate** of a polynomial of total degree at most two:
moving the `i`-th coordinate by `s` changes the value by
`s ∂ᵢR + s²/2 ∂ᵢ²R` (the second derivative being constant). -/
theorem eval_update_add [DecidableEq σ] (R : MvPolynomial σ ℝ) (hR : R.totalDegree ≤ 2) (v : σ → ℝ) (i : σ)
    (s : ℝ) :
    MvPolynomial.eval (Function.update v i (v i + s)) R =
      MvPolynomial.eval v R + s * MvPolynomial.eval v (MvPolynomial.pderiv i R) +
        s ^ 2 / 2 * MvPolynomial.eval v (MvPolynomial.pderiv i (MvPolynomial.pderiv i R)) := by
  have h := eval_add_of_natDegree_le_two (coordPoly v i R)
    ((natDegree_coordPoly_le v i R).trans hR) (v i) s
  rw [derivative_coordPoly, derivative_coordPoly, eval_coordPoly, eval_coordPoly, eval_coordPoly,
    eval_coordPoly, Function.update_eq_self] at h
  exact h

/-- The hidden derivative of a test of total degree at most two is affine in the hidden
coordinate. -/
theorem eval_update_add_pderiv [DecidableEq σ] (R : MvPolynomial σ ℝ) (hR : R.totalDegree ≤ 2) (v : σ → ℝ)
    (i : σ) (s : ℝ) :
    MvPolynomial.eval (Function.update v i (v i + s)) (MvPolynomial.pderiv i R) =
      MvPolynomial.eval v (MvPolynomial.pderiv i R) +
        s * MvPolynomial.eval v (MvPolynomial.pderiv i (MvPolynomial.pderiv i R)) := by
  have hd : (MvPolynomial.pderiv i R).totalDegree ≤ 2 :=
    (totalDegree_pderiv_le_pred R i).trans (by omega)
  rw [eval_update_add (MvPolynomial.pderiv i R) hd v i s, pderiv_pderiv_pderiv_eq_zero R hR i]
  simp

/-- **The nearest root of a quadratic** (paper `tex-03-comparison.tex`, display
`a02:nearest-quadratic-root`).  For the quadratic `s ↦ p + q s + c/2 s²` with slope `q ≠ 0`
and `2 |c p| ≤ q² / 2`, the discriminant `D = q² - 2 c p` is positive, and the root `s`
on the side where the slope keeps the sign of `q` satisfies `q + c s = sign(q) √D` and
`|s| = 2 |p| / (|q| + √D) ≤ 2 |p| / |q|`. -/
theorem quadratic_nearest_root (p q c : ℝ) (hq : q ≠ 0) (hsmall : 2 * |c * p| ≤ q ^ 2 / 2) :
    0 < q ^ 2 - 2 * c * p ∧ ∃ s : ℝ, p + q * s + c / 2 * s ^ 2 = 0 ∧
      0 < (q + c * s) * q ∧ |q + c * s| = Real.sqrt (q ^ 2 - 2 * c * p) ∧
      |s| = 2 * |p| / (|q| + Real.sqrt (q ^ 2 - 2 * c * p)) ∧ |s| ≤ 2 * |p| / |q| := by
  set D := q ^ 2 - 2 * c * p with hD
  have hq2 : 0 < q ^ 2 := by positivity
  have hDpos : 0 < D := by
    have : c * p ≤ |c * p| := le_abs_self _
    nlinarith
  set r := Real.sqrt D with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hDpos
  have hr2 : r ^ 2 = D := Real.sq_sqrt hDpos.le
  set σ' : ℝ := if 0 < q then 1 else -1 with hσ
  have hσ2 : σ' ^ 2 = 1 := by simp only [hσ]; split_ifs <;> norm_num
  have hσq : σ' * q = |q| := by
    simp only [hσ]; split_ifs with h
    · rw [abs_of_pos h]; ring
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hq)]; ring
  have hden : q + σ' * r ≠ 0 := by
    intro h0
    have : σ' * (q + σ' * r) = |q| + r := by rw [mul_add, hσq, ← mul_assoc, ← sq, hσ2, one_mul]
    rw [h0, mul_zero] at this
    have : 0 < |q| + r := by positivity
    linarith
  have habsden : |q + σ' * r| = |q| + r := by
    have h1 : σ' * (q + σ' * r) = |q| + r := by rw [mul_add, hσq, ← mul_assoc, ← sq, hσ2, one_mul]
    have h2 : |σ'| = 1 := by simp only [hσ]; split_ifs <;> norm_num
    rw [← one_mul |q + σ' * r|, ← h2, ← abs_mul, h1, abs_of_pos (by positivity)]
  set s := -2 * p / (q + σ' * r) with hs
  have hslope : q + c * s = σ' * r := by
    rw [hs]
    field_simp
    nlinarith [hr2, hσ2]
  have hsden : s * (q + σ' * r) = -2 * p := by rw [hs]; field_simp
  have h2 : |σ'| = 1 := by simp only [hσ]; split_ifs <;> norm_num
  refine ⟨hDpos, s, ?_, ?_, ?_, ?_, ?_⟩
  · have : p + q * s + c / 2 * s ^ 2 = p + s * (q + (q + c * s)) / 2 := by ring
    rw [this, hslope, hsden]; ring
  · rw [hslope]
    have : σ' * r * q = r * |q| := by rw [mul_comm σ' r, mul_assoc, hσq]
    rw [this]
    exact mul_pos hr0 (abs_pos.mpr hq)
  · rw [hslope, abs_mul, abs_of_pos hr0, h2, one_mul]
  · rw [hs, abs_div, habsden, abs_mul]; norm_num
  · rw [hs, abs_div, habsden, abs_mul]
    norm_num
    apply div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr hq)
    linarith

/-- **Nearest simple root of a quadratic test in one coordinate.**  If `R` has total
degree at most two, its `i`-th derivative `q` at `v` is nonzero and the curvature `c`
satisfies `2 |c R(v)| ≤ q² / 2`, then moving the `i`-th coordinate by at most
`2 |R(v)| / |q|` reaches a zero of `R` at which the `i`-th derivative keeps the sign of `q`
and has absolute value `√(q² - 2 c R(v))`. -/
theorem exists_nearest_root_update [DecidableEq σ] (R : MvPolynomial σ ℝ) (hR : R.totalDegree ≤ 2)
    (v : σ → ℝ) (i : σ)
    (hq : MvPolynomial.eval v (MvPolynomial.pderiv i R) ≠ 0)
    (hsmall : 2 * |MvPolynomial.eval v (MvPolynomial.pderiv i (MvPolynomial.pderiv i R)) *
        MvPolynomial.eval v R| ≤ (MvPolynomial.eval v (MvPolynomial.pderiv i R)) ^ 2 / 2) :
    ∃ w : ℝ, MvPolynomial.eval (Function.update v i w) R = 0 ∧
      |w - v i| ≤ 2 * |MvPolynomial.eval v R| / |MvPolynomial.eval v (MvPolynomial.pderiv i R)| ∧
      0 < MvPolynomial.eval (Function.update v i w) (MvPolynomial.pderiv i R) *
        MvPolynomial.eval v (MvPolynomial.pderiv i R) ∧
      |MvPolynomial.eval (Function.update v i w) (MvPolynomial.pderiv i R)| =
        Real.sqrt ((MvPolynomial.eval v (MvPolynomial.pderiv i R)) ^ 2 -
          2 * MvPolynomial.eval v (MvPolynomial.pderiv i (MvPolynomial.pderiv i R)) *
            MvPolynomial.eval v R) := by
  set p := MvPolynomial.eval v R
  set q := MvPolynomial.eval v (MvPolynomial.pderiv i R)
  set c := MvPolynomial.eval v (MvPolynomial.pderiv i (MvPolynomial.pderiv i R))
  obtain ⟨-, s, hroot, hsign, habs, -, hle⟩ := quadratic_nearest_root p q c hq hsmall
  refine ⟨v i + s, ?_, ?_, ?_, ?_⟩
  · rw [eval_update_add R hR v i s]
    linarith [hroot]
  · simpa using hle
  · rw [eval_update_add_pderiv R hR v i s]
    change 0 < (q + s * c) * q
    rw [mul_comm s c]; exact hsign
  · rw [eval_update_add_pderiv R hR v i s]
    change |q + s * c| = _
    rw [mul_comm s c]; exact habs

end

end Submission.Lib.K4HiddenQuadratic
