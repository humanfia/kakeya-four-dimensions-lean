/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4CubicTests.HomogeneousBounds

open MvPolynomial

namespace Submission.Lib.K4CubicTests

/-- The formal coordinate derivatives give the derivative of evaluation along
any coordinate-wise differentiable real curve. -/
theorem hasDerivAt_eval_polynomial_curve (F : MvPolynomial (Fin 3) ℝ)
    (z : ℝ → Fin 3 → ℝ) (z' : Fin 3 → ℝ) (t : ℝ)
    (hz : ∀ i, HasDerivAt (fun s => z s i) (z' i) t) :
    HasDerivAt (fun s => MvPolynomial.eval (z s) F)
      (∑ i : Fin 3, MvPolynomial.eval (z t) (pderiv i F) * z' i) t := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t a
  | add p q hp hq =>
      simpa only [map_add, add_mul, Finset.sum_add_distrib] using hp.fun_add hq
  | mul_X p j hp =>
      convert hp.fun_mul (hz j) using 1
      · funext s
        simp only [map_mul, eval_X, Pi.mul_apply]
      · simp only [pderiv_mul, pderiv_X, map_add, map_mul, eval_X, Fin.sum_univ_three]
        fin_cases j <;> simp [Pi.single_apply] <;> ring

private theorem abs_sum_three_le (f : Fin 3 → ℝ) (M : ℝ) (hf : ∀ i, |f i| ≤ M) :
    |∑ i, f i| ≤ 3 * M := by
  calc
    _ ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, M := Finset.sum_le_sum fun i _ => hf i
    _ = _ := by simp

/-- A point perturbation bound for a homogeneous polynomial, with explicit
coefficient and coordinate losses. This transfers tests to restored conic
points without an implicit compactness constant. -/
theorem homogeneous_eval_sub_abs_le (F : MvPolynomial (Fin 3) ℝ)
    (n : ℕ) (hF : F.IsHomogeneous (n + 1)) (A M Δ : ℝ)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hΔ : 0 ≤ Δ) (hcoeff : ∀ m, |F.coeff m| ≤ M)
    (x y : Fin 3 → ℝ) (hx : ∀ i, |x i| ≤ A) (hy : ∀ i, |y i| ≤ A)
    (hdiff : ∀ i, |y i - x i| ≤ Δ) :
    |MvPolynomial.eval y F - MvPolynomial.eval x F| ≤
      (3 : ℝ) ^ (n + 1) * A ^ n * ((n + 1 : ℕ) : ℝ) * M * Δ := by
  let z : ℝ → Fin 3 → ℝ := fun t i => x i + t * (y i - x i)
  let f : ℝ → ℝ := fun t => MvPolynomial.eval (z t) F
  let f' : ℝ → ℝ := fun t => ∑ i : Fin 3, MvPolynomial.eval (z t) (pderiv i F) * (y i - x i)
  let K : ℝ := (3 : ℝ) ^ n * A ^ n * (((n + 1 : ℕ) : ℝ) * M)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hz (t : ℝ) (i : Fin 3) : HasDerivAt (fun s => z s i) (y i - x i) t := by
    simpa only [z, one_mul, id_eq] using
      HasDerivAt.const_add (x i) ((hasDerivAt_id t).mul_const (y i - x i))
  have hf (t : ℝ) : HasDerivAt f (f' t) t :=
    hasDerivAt_eval_polynomial_curve F z (fun i => y i - x i) t (hz t)
  have hzc (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin 3) : |z t i| ≤ A := by
    have heq : z t i = (1 - t) * x i + t * y i := by dsimp [z]; ring
    rw [heq]
    calc
      _ ≤ |(1 - t) * x i| + |t * y i| := abs_add_le _ _
      _ = (1 - t) * |x i| + t * |y i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
      _ ≤ (1 - t) * A + t * A := add_le_add
        (mul_le_mul_of_nonneg_left (hx i) (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left (hy i) ht.1)
      _ = _ := by ring
  have hdc (i : Fin 3) (m : Fin 3 →₀ ℕ) : |(pderiv i F).coeff m| ≤ ((n + 1 : ℕ) : ℝ) * M :=
    coeff_pderiv_abs_le_of_totalDegree F (n + 1) hF.totalDegree_le M hM hcoeff i m
  have hdv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin 3) :
      |MvPolynomial.eval (z t) (pderiv i F)| ≤ K :=
    homogeneous_eval_abs_le A hA (z t) (hzc t ht) n (pderiv i F)
      (by simpa using hF.pderiv) _ (by positivity) (hdc i)
  have hbound (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) : ‖f' t‖ ≤ 3 * (K * Δ) := by
    rw [Real.norm_eq_abs]
    apply abs_sum_three_le _ _
    intro i
    rw [abs_mul]
    exact mul_le_mul (hdv t ⟨ht.1, ht.2.le⟩ i) (hdiff i) (abs_nonneg _) hK
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hf t).hasDerivWithinAt) hbound
  have hz0 : z 0 = x := by funext i; simp [z]
  have hz1 : z 1 = y := by funext i; dsimp [z]; ring
  calc
    |MvPolynomial.eval y F - MvPolynomial.eval x F| ≤ 3 * (K * Δ) := by
      simpa only [f, hz0, hz1, Real.norm_eq_abs] using hmv
    _ = _ := by dsimp [K]; rw [pow_succ]; ring

/-- Transfer a small homogeneous polynomial test across a controlled point
perturbation, using the coefficient bound to control its variation. -/
theorem homogeneous_eval_test_transfer (F : MvPolynomial (Fin 3) ℝ)
    (n : ℕ) (hF : F.IsHomogeneous (n + 1)) (A M Δ ε : ℝ)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hΔ : 0 ≤ Δ) (hcoeff : ∀ m, |F.coeff m| ≤ M)
    (x y : Fin 3 → ℝ) (hx : ∀ i, |x i| ≤ A) (hy : ∀ i, |y i| ≤ A)
    (hdiff : ∀ i, |y i - x i| ≤ Δ) (hsmall : |MvPolynomial.eval x F| ≤ ε) :
    |MvPolynomial.eval y F| ≤ ε + (3 : ℝ) ^ (n + 1) * A ^ n * ((n + 1 : ℕ) : ℝ) * M * Δ := by
  have hchange := homogeneous_eval_sub_abs_le F n hF A M Δ hA hM hΔ hcoeff x y hx hy hdiff
  calc
    |MvPolynomial.eval y F| = |(MvPolynomial.eval y F - MvPolynomial.eval x F) + MvPolynomial.eval x F| := by
      congr 1
      ring
    _ ≤ |MvPolynomial.eval y F - MvPolynomial.eval x F| + |MvPolynomial.eval x F| := abs_add_le _ _
    _ ≤ _ := by linarith

end Submission.Lib.K4CubicTests
