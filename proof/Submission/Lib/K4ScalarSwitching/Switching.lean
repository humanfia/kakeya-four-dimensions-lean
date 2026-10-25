/-
Adapted from: here:o062
Original proof: x0511, branch x0511, commit bf52299; retained source-credit comment follows.
Owned source: Submission/Obl/k4_scalar_mesh_projection/Switching.lean.
-/

/- From o062 session x0511, branch x0511, commit bf52299;
original file Submission/Obl/k4_scalar_mesh_projection/Switching.lean. -/

import Mathlib

/-!
The scalar four-leg switching calculation. Two pairs of velocity directions
form bases of the time-position plane. The first derivatives of the maximal
endpoint minors detect the skew part of the field derivative.
-/

namespace Submission.Lib.K4ScalarSwitching.Switching

open MvPolynomial

theorem partials_commute {σ : Type*} (P : MvPolynomial σ ℝ) (i j : σ) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  by_cases hij : i = j
  · subst j; rfl
  ext m
  simp only [coeff_pderiv]
  rw [show m + Finsupp.single i 1 + Finsupp.single j 1 =
      m + Finsupp.single j 1 + Finsupp.single i 1 by abel]
  simp only [Finsupp.add_apply, Finsupp.single_apply, hij, Ne.symm hij,
    ite_eq_right_of_eq_false, add_zero]
  ring

theorem partial_eval_zero_eq_coeff {σ : Type*} (P : MvPolynomial σ ℝ) (i : σ) :
    eval (0 : σ → ℝ) (pderiv i P) = P.coeff (Finsupp.single i 1) := by
  rw [eval_zero]
  change (pderiv i P).coeff 0 = _
  rw [coeff_pderiv]
  simp

/-- The maximal minor using the first two base columns and the `j`th one.
The base columns are `(1,v_i)`. -/
noncomputable def endpointMinor (R : MvPolynomial (Fin 4) ℝ)
    (v : Fin 4 → ℝ) (j : Fin 4) : MvPolynomial (Fin 4) ℝ :=
  C (v 1 - v 0) * pderiv j R + C (v 0 - v j) * pderiv 1 R +
    C (v j - v 1) * pderiv 0 R

theorem eval_endpointMinor (R : MvPolynomial (Fin 4) ℝ) (v x : Fin 4 → ℝ)
    (j : Fin 4) :
    eval x (endpointMinor R v j) = Matrix.det
      !![1, 1, 1; v 0, v 1, v j;
        eval x (pderiv 0 R), eval x (pderiv 1 R), eval x (pderiv j R)] := by
  simp [endpointMinor, Matrix.det_fin_three]
  ring

noncomputable def hessian (R : MvPolynomial (Fin 4) ℝ) (x : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ := fun i j => eval x (pderiv i (pderiv j R))

theorem hessian_symm (R : MvPolynomial (Fin 4) ℝ) (x : Fin 4 → ℝ)
    (i j : Fin 4) : hessian R x i j = hessian R x j i := by
  unfold hessian
  rw [partials_commute R i j]

def minorDerivative (v : Fin 4 → ℝ) (H : Matrix (Fin 4) (Fin 4) ℝ)
    (i j : Fin 4) : ℝ :=
  (v 1 - v 0) * H i j + (v 0 - v j) * H i 1 + (v j - v 1) * H i 0

theorem eval_partial_endpointMinor (R : MvPolynomial (Fin 4) ℝ)
    (v x : Fin 4 → ℝ) (i j : Fin 4) :
    eval x (pderiv i (endpointMinor R v j)) = minorDerivative v (hessian R x) i j := by
  simp only [endpointMinor, map_add, pderiv_C_mul, map_mul, eval_C,
    minorDerivative, hessian]

/-- The two bases recover the skew derivative from four derivatives of
maximal minors. Only the symmetry of the first Hessian block is used. -/
theorem curl_minor_identity (v : Fin 4 → ℝ) (H : Matrix (Fin 4) (Fin 4) ℝ)
    (At Ay Bt By : ℝ) (hsym : H 0 1 = H 1 0)
    (hcross : ∀ i j : Fin 4, i.val < 2 → 2 ≤ j.val →
      H i j = At + v i * Ay + v j * Bt + v i * v j * By) :
    (v 1 - v 0) ^ 2 * (v 3 - v 2) * (Bt - Ay) =
      (v 1 - v 2) * minorDerivative v H 0 3 +
      (v 3 - v 1) * minorDerivative v H 0 2 +
      (v 0 - v 3) * minorDerivative v H 1 2 +
      (v 2 - v 0) * minorDerivative v H 1 3 := by
  unfold minorDerivative
  rw [hcross 0 2 (by decide) (by decide), hcross 0 3 (by decide) (by decide),
    hcross 1 2 (by decide) (by decide), hcross 1 3 (by decide) (by decide), hsym]
  ring

theorem curl_bound_of_minor_derivatives (v : Fin 4 → ℝ)
    (H : Matrix (Fin 4) (Fin 4) ℝ) (At Ay Bt By : ℝ) {K η δI δJ : ℝ}
    (hK : 0 ≤ K) (_hη : 0 ≤ η) (hI : 0 < δI) (hJ : 0 < δJ)
    (hv : ∀ i, |v i| ≤ K) (hdetI : δI ≤ |v 1 - v 0|)
    (hdetJ : δJ ≤ |v 3 - v 2|) (hsym : H 0 1 = H 1 0)
    (hcross : ∀ i j : Fin 4, i.val < 2 → 2 ≤ j.val →
      H i j = At + v i * Ay + v j * Bt + v i * v j * By)
    (hminor : ∀ i j : Fin 4, i.val < 2 → 2 ≤ j.val →
      |minorDerivative v H i j| ≤ η) :
    |Bt - Ay| ≤ (8 * K * η) / (δI ^ 2 * δJ) := by
  have hcoef (i j : Fin 4) : |v i - v j| ≤ 2 * K :=
    (abs_sub _ _).trans (by linarith [hv i, hv j])
  have hterm (a b i j : Fin 4) (hi : i.val < 2) (hj : 2 ≤ j.val) :
      |(v a - v b) * minorDerivative v H i j| ≤ 2 * K * η := by
    rw [abs_mul]
    exact mul_le_mul (hcoef a b) (hminor i j hi hj) (abs_nonneg _) (by positivity)
  have hsum : |(v 1 - v 0) ^ 2 * (v 3 - v 2) * (Bt - Ay)| ≤ 8 * K * η := by
    rw [curl_minor_identity v H At Ay Bt By hsym hcross]
    calc
      _ ≤ |(v 1 - v 2) * minorDerivative v H 0 3| +
          |(v 3 - v 1) * minorDerivative v H 0 2| +
          |(v 0 - v 3) * minorDerivative v H 1 2| +
          |(v 2 - v 0) * minorDerivative v H 1 3| := by
        let a := (v 1 - v 2) * minorDerivative v H 0 3
        let b := (v 3 - v 1) * minorDerivative v H 0 2
        let c := (v 0 - v 3) * minorDerivative v H 1 2
        let d := (v 2 - v 0) * minorDerivative v H 1 3
        change |a + b + c + d| ≤ |a| + |b| + |c| + |d|
        have h₁ := abs_add_le a b
        have h₂ := abs_add_le (a + b) c
        have h₃ := abs_add_le (a + b + c) d
        linarith
      _ ≤ _ := by
        linarith [hterm 1 2 0 3 (by decide) (by decide),
          hterm 3 1 0 2 (by decide) (by decide),
          hterm 0 3 1 2 (by decide) (by decide),
          hterm 2 0 1 3 (by decide) (by decide)]
  have hscaled : (δI ^ 2 * δJ) * |Bt - Ay| ≤ 8 * K * η := by
    apply le_trans ?_ hsum
    rw [abs_mul, abs_mul, abs_pow]
    gcongr
  exact (le_div_iff₀ (mul_pos (sq_pos_of_pos hI) hJ)).mpr (by
    simpa only [mul_comm] using hscaled)

/-- In subpower units the inverse determinants of both bases cost only a
fixed power of the same loss factor. -/
theorem polynomial_curl_bound (R : MvPolynomial (Fin 4) ℝ) (v x : Fin 4 → ℝ)
    (At Ay Bt By : ℝ) {K η : ℝ} (hK : 1 ≤ K) (hη : 0 ≤ η)
    (hv : ∀ i, |v i| ≤ K) (hdetI : 1 / K ≤ |v 1 - v 0|)
    (hdetJ : 1 / K ≤ |v 3 - v 2|)
    (hcross : ∀ i j : Fin 4, i.val < 2 → 2 ≤ j.val →
      hessian R x i j = At + v i * Ay + v j * Bt + v i * v j * By)
    (hminor : ∀ i j : Fin 4, i.val < 2 → 2 ≤ j.val →
      |eval x (pderiv i (endpointMinor R v j))| ≤ η) :
    |Bt - Ay| ≤ 8 * K ^ 4 * η := by
  have hKpos : 0 < K := by linarith
  have h := curl_bound_of_minor_derivatives v (hessian R x) At Ay Bt By hKpos.le hη
    (by positivity : 0 < 1 / K) (by positivity : 0 < 1 / K) hv hdetI hdetJ
    (hessian_symm R x 0 1) hcross (by
      intro i j hi hj
      simpa only [eval_partial_endpointMinor] using hminor i j hi hj)
  convert h using 1
  field_simp

/-- A nonzero scalar curl forces a large first jet of at least one of the
two endpoint minors. -/
theorem exists_large_minor_derivative (R : MvPolynomial (Fin 4) ℝ)
    (v x : Fin 4 → ℝ) (At Ay Bt By : ℝ) {K η : ℝ} (hK : 1 ≤ K) (hη : 0 ≤ η)
    (hv : ∀ i, |v i| ≤ K) (hdetI : 1 / K ≤ |v 1 - v 0|)
    (hdetJ : 1 / K ≤ |v 3 - v 2|)
    (hcross : ∀ i j : Fin 4, i.val < 2 → 2 ≤ j.val →
      hessian R x i j = At + v i * Ay + v j * Bt + v i * v j * By)
    (hskew : 8 * K ^ 4 * η < |Bt - Ay|) :
    ∃ i j : Fin 4, i.val < 2 ∧ 2 ≤ j.val ∧
      η < |eval x (pderiv i (endpointMinor R v j))| := by
  by_contra hn
  have hsmall : ∀ i j : Fin 4, i.val < 2 → 2 ≤ j.val →
      |eval x (pderiv i (endpointMinor R v j))| ≤ η := by
    intro i j hi hj
    exact not_lt.mp (fun h => hn ⟨i, j, hi, hj, h⟩)
  have h := polynomial_curl_bound R v x At Ay Bt By hK hη hv hdetI hdetJ hcross hsmall
  linarith

/-- Chain rule for polynomial substitution, kept algebraic so it also
applies to the extra integration variable in a switched leg. -/
theorem partial_aeval {σ τ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (f : σ → MvPolynomial τ ℝ) (i : τ) :
    pderiv i (aeval f P) = ∑ j : σ, aeval f (pderiv j P) * pderiv i (f j) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
    simp only [map_add, hP, hQ, add_mul, Finset.sum_add_distrib]
  | mul_X P k hP =>
    have hprod (j : σ) : aeval f (pderiv j (P * X k)) =
        aeval f (pderiv j P) * f k + (if j = k then aeval f P else 0) := by
      by_cases hj : j = k
      · subst j
        simp [mul_comm, add_comm]
      · simp [hj, Ne.symm hj, mul_comm]
    rw [map_mul, aeval_X, pderiv_mul, hP]
    simp_rw [hprod, add_mul]
    rw [Finset.sum_add_distrib]
    have hsum : (∑ j : σ, aeval f (pderiv j P) * f k * pderiv i (f j)) =
        (∑ j : σ, aeval f (pderiv j P) * pderiv i (f j)) * f k := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum]
    simp

end Submission.Lib.K4ScalarSwitching.Switching
