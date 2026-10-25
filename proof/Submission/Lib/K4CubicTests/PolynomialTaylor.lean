/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib

open MvPolynomial

namespace Submission.Lib.K4CubicTests

/-- The coordinate-derivative formula along an arbitrary differentiable
curve, for any finite set of polynomial variables. -/
theorem hasDerivAt_eval_finite_polynomial_curve {ι : Type*} [Fintype ι]
    (F : MvPolynomial ι ℝ) (z : ℝ → ι → ℝ) (z' : ι → ℝ) (t : ℝ)
    (hz : ∀ i, HasDerivAt (fun s => z s i) (z' i) t) :
    HasDerivAt (fun s => MvPolynomial.eval (z s) F)
      (∑ i, MvPolynomial.eval (z t) (pderiv i F) * z' i) t := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t a
  | add p q hp hq =>
      simpa only [map_add, add_mul, Finset.sum_add_distrib] using hp.fun_add hq
  | mul_X p j hp =>
      convert hp.fun_mul (hz j) using 1
      · funext s
        simp only [map_mul, eval_X]
      · have hdelta (i : ι) : MvPolynomial.eval (z t) (pderiv i (X j)) =
            if i = j then 1 else 0 := by
          by_cases hij : i = j
          · subst i
            simp
          · rw [pderiv_X_of_ne (Ne.symm hij)]
            simp [hij]
        simp only [pderiv_mul, map_add, map_mul, eval_X, hdelta, add_mul,
          Finset.sum_add_distrib]
        simp [Finset.mul_sum, mul_ite, ite_mul, mul_left_comm, mul_comm]

/-- The formal derivative in a fixed direction. -/
noncomputable def polynomialDirectionalDerivative {ι : Type*} [Fintype ι]
    (v : ι → ℝ) (F : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  ∑ i, C (v i) * pderiv i F

theorem hasDerivAt_eval_polynomial_line {ι : Type*} [Fintype ι]
    (F : MvPolynomial ι ℝ) (c v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => MvPolynomial.eval (fun i => c i + s * v i) F)
      (MvPolynomial.eval (fun i => c i + t * v i) (polynomialDirectionalDerivative v F)) t := by
  have hz (i : ι) : HasDerivAt (fun s => c i + s * v i) (v i) t := by
    simpa only [one_mul, id_eq] using
      HasDerivAt.const_add (c i) ((hasDerivAt_id t).mul_const (v i))
  simpa only [polynomialDirectionalDerivative, map_sum, map_mul, eval_C, mul_comm] using
    hasDerivAt_eval_finite_polynomial_curve F (fun s i => c i + s * v i) v t hz

/-- A derivative bound controls displacement on the unit interval. -/
private theorem displacement_bound (f g : ℝ → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hfg : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g t| ≤ M) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, |f t - f 0| ≤ M := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hfg t ht).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using hg t ⟨ht.1, ht.2.le⟩)
  intro t ht
  have he : |f t - f 0| ≤ M * t := by
    simpa only [Real.norm_eq_abs, sub_zero] using h t ht
  exact he.trans (mul_le_of_le_one_right hM ht.2)

/-- A coarse, explicit quadratic Taylor remainder from a derivative chain.
The three derivatives need only exist on the closed unit interval. -/
theorem quadratic_taylor_error_of_derivative_chain (f₀ f₁ f₂ f₃ : ℝ → ℝ)
    (M : ℝ) (hM : 0 ≤ M)
    (h₀ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f₀ (f₁ t) t)
    (h₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f₁ (f₂ t) t)
    (h₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f₂ (f₃ t) t)
    (h₃ : ∀ t ∈ Set.Icc (0 : ℝ) 1, |f₃ t| ≤ M) :
    |f₀ 1 - (f₀ 0 + f₁ 0 + f₂ 0 / 2)| ≤ M := by
  have hb₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, |f₂ t - f₂ 0| ≤ M :=
    displacement_bound f₂ f₃ M hM h₂ h₃
  let g₁ : ℝ → ℝ := fun t => f₁ t - f₁ 0 - t * f₂ 0
  have hd₁ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt g₁ (f₂ t - f₂ 0) t := by
    convert ((h₁ t ht).sub_const (f₁ 0)).fun_sub
      ((hasDerivAt_id t).mul_const (f₂ 0)) using 1 <;> (try dsimp [g₁]) <;> ring
  have hb₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g₁ t| ≤ M := by
    have h := displacement_bound g₁ (fun t => f₂ t - f₂ 0) M hM hd₁ hb₂
    simpa [g₁] using h
  let g₀ : ℝ → ℝ := fun t => f₀ t - f₀ 0 - t * f₁ 0 - t ^ 2 * (f₂ 0 / 2)
  have hd₀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt g₀ (g₁ t) t := by
    convert (((h₀ t ht).sub_const (f₀ 0)).fun_sub
      ((hasDerivAt_id t).mul_const (f₁ 0))).fun_sub
      (((hasDerivAt_id t).pow 2).mul_const (f₂ 0 / 2)) using 1 <;>
      dsimp [g₀, g₁] <;> ring
  have h := displacement_bound g₀ g₁ M hM hd₀ hb₁ 1 (by norm_num)
  calc
    |f₀ 1 - (f₀ 0 + f₁ 0 + f₂ 0 / 2)| = |g₀ 1 - g₀ 0| := by
      congr 1
      dsimp [g₀]
      ring
    _ ≤ M := h

/-- A polynomial restricted to a line admits its quadratic Taylor fit with
an explicit error equal to a bound for its third directional derivative. -/
theorem polynomial_line_quadratic_taylor_abs_le {ι : Type*} [Fintype ι]
    (F : MvPolynomial ι ℝ) (c v : ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hthird : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |MvPolynomial.eval (fun i => c i + t * v i)
        (polynomialDirectionalDerivative v (polynomialDirectionalDerivative v
          (polynomialDirectionalDerivative v F)))| ≤ M) :
    |MvPolynomial.eval (fun i => c i + v i) F -
      (MvPolynomial.eval c F + MvPolynomial.eval c (polynomialDirectionalDerivative v F) +
        MvPolynomial.eval c (polynomialDirectionalDerivative v (polynomialDirectionalDerivative v F)) / 2)| ≤ M := by
  have h := quadratic_taylor_error_of_derivative_chain
    (fun t => MvPolynomial.eval (fun i => c i + t * v i) F)
    (fun t => MvPolynomial.eval (fun i => c i + t * v i) (polynomialDirectionalDerivative v F))
    (fun t => MvPolynomial.eval (fun i => c i + t * v i)
      (polynomialDirectionalDerivative v (polynomialDirectionalDerivative v F)))
    (fun t => MvPolynomial.eval (fun i => c i + t * v i)
      (polynomialDirectionalDerivative v (polynomialDirectionalDerivative v (polynomialDirectionalDerivative v F))))
    M hM (fun t _ => hasDerivAt_eval_polynomial_line F c v t)
    (fun t _ => hasDerivAt_eval_polynomial_line (polynomialDirectionalDerivative v F) c v t)
    (fun t _ => hasDerivAt_eval_polynomial_line
      (polynomialDirectionalDerivative v (polynomialDirectionalDerivative v F)) c v t) hthird
  simpa only [one_mul, zero_mul, add_zero] using h

/-- The coordinate expression for the quadratic Taylor polynomial about `c`,
written in displacement variables. -/
noncomputable def polynomialQuadraticTaylor {ι : Type*} [Fintype ι]
    (F : MvPolynomial ι ℝ) (c : ι → ℝ) : MvPolynomial ι ℝ :=
  C (MvPolynomial.eval c F) +
    (∑ i, C (MvPolynomial.eval c (pderiv i F)) * X i) +
    C (1 / 2 : ℝ) * (∑ i, ∑ j, C (MvPolynomial.eval c (pderiv i (pderiv j F))) * X i * X j)

theorem polynomialQuadraticTaylor_totalDegree_le {ι : Type*} [Fintype ι]
    (F : MvPolynomial ι ℝ) (c : ι → ℝ) : (polynomialQuadraticTaylor F c).totalDegree ≤ 2 := by
  classical
  have hlinear : (∑ i : ι, C (MvPolynomial.eval c (pderiv i F)) * X i).totalDegree ≤ 1 :=
    totalDegree_finsetSum_le fun i _ => (isHomogeneous_C_mul_X _ _).totalDegree_le
  have hquadratic : (C (1 / 2 : ℝ) *
      (∑ i : ι, ∑ j : ι, C (MvPolynomial.eval c (pderiv i (pderiv j F))) * X i * X j)).IsHomogeneous 2 :=
    (IsHomogeneous.sum _ _ _ fun i _ => IsHomogeneous.sum _ _ _ fun j _ =>
      (isHomogeneous_C_mul_X _ _).mul (isHomogeneous_X ℝ j)).C_mul _
  unfold polynomialQuadraticTaylor
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    rw [totalDegree_C]
    exact max_le (by omega) (hlinear.trans (by omega))
  · exact hquadratic.totalDegree_le

theorem eval_polynomialQuadraticTaylor {ι : Type*} [Fintype ι]
    (F : MvPolynomial ι ℝ) (c v : ι → ℝ) :
    MvPolynomial.eval v (polynomialQuadraticTaylor F c) =
      MvPolynomial.eval c F + MvPolynomial.eval c (polynomialDirectionalDerivative v F) +
        MvPolynomial.eval c (polynomialDirectionalDerivative v (polynomialDirectionalDerivative v F)) / 2 := by
  classical
  simp only [polynomialQuadraticTaylor, polynomialDirectionalDerivative, map_add, map_sum,
    map_mul, eval_C, eval_X, pderiv_C_mul, Finset.mul_sum, div_eq_mul_inv]
  simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/-- The same fit is one fixed polynomial of total degree at most two for
all displacements whose joining segment satisfies the derivative bound. -/
theorem polynomial_quadratic_taylor_error_le {ι : Type*} [Fintype ι]
    (F : MvPolynomial ι ℝ) (c v : ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hthird : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |MvPolynomial.eval (fun i => c i + t * v i)
        (polynomialDirectionalDerivative v (polynomialDirectionalDerivative v
          (polynomialDirectionalDerivative v F)))| ≤ M) :
    |MvPolynomial.eval (fun i => c i + v i) F -
      MvPolynomial.eval v (polynomialQuadraticTaylor F c)| ≤ M := by
  rw [eval_polynomialQuadraticTaylor]
  exact polynomial_line_quadratic_taylor_abs_le F c v M hM hthird

/-- The third directional derivative is the cubic contraction of the
coordinate third derivatives, in any finite number of variables. -/
theorem eval_polynomialDirectionalDerivative_cube {ι : Type*} [Fintype ι]
    (F : MvPolynomial ι ℝ) (x v : ι → ℝ) :
    MvPolynomial.eval x (polynomialDirectionalDerivative v (polynomialDirectionalDerivative v
      (polynomialDirectionalDerivative v F))) =
      ∑ i, ∑ j, ∑ k, v i * v j * v k * MvPolynomial.eval x (pderiv i (pderiv j (pderiv k F))) := by
  classical
  simp [polynomialDirectionalDerivative, map_sum, pderiv_C_mul, Finset.mul_sum, mul_assoc]

private theorem finite_abs_sum_bound {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (M : ℝ) (hf : ∀ i, |f i| ≤ M) :
    |∑ i, f i| ≤ (Fintype.card ι : ℝ) * M := by
  calc
    _ ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, M := Finset.sum_le_sum fun i _ => hf i
    _ = _ := by simp

/-- An explicit bound on a third directional derivative from coordinate
third-derivative bounds. -/
theorem third_directional_eval_abs_le_of_partial_bounds {ι : Type*} [Fintype ι]
    (F : MvPolynomial ι ℝ) (x v : ι → ℝ) (B M : ℝ) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hv : ∀ i, |v i| ≤ B)
    (hpartial : ∀ i j k, |MvPolynomial.eval x (pderiv i (pderiv j (pderiv k F)))| ≤ M) :
    |MvPolynomial.eval x (polynomialDirectionalDerivative v (polynomialDirectionalDerivative v
      (polynomialDirectionalDerivative v F)))| ≤ (Fintype.card ι : ℝ) ^ 3 * B ^ 3 * M := by
  classical
  rw [eval_polynomialDirectionalDerivative_cube]
  have hterm (i j k : ι) :
      |v i * v j * v k * MvPolynomial.eval x (pderiv i (pderiv j (pderiv k F)))| ≤ B ^ 3 * M := by
    simp only [abs_mul]
    calc
      _ ≤ (B * B * B) * M := mul_le_mul
        (mul_le_mul (mul_le_mul (hv i) (hv j) (abs_nonneg _) hB) (hv k)
          (abs_nonneg _) (mul_nonneg hB hB)) (hpartial i j k) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hinner (i j : ι) := finite_abs_sum_bound _ (B ^ 3 * M) (hterm i j)
  have hmid (i : ι) := finite_abs_sum_bound _ ((Fintype.card ι : ℝ) * (B ^ 3 * M)) (hinner i)
  convert finite_abs_sum_bound _ ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) * (B ^ 3 * M))) hmid using 1 <;> ring

end Submission.Lib.K4CubicTests
