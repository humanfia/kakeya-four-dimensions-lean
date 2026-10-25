/-
Copied with the namespace renamed from o144 (k4_seven_direction_local_degree_restoration),
branch x0492, commit 9cac1f6, file Submission/Obl/k4_seven_direction_local_degree_restoration/Kit/ConicConditioning.lean.
That file's own header follows.
-/
/-
Copied with the namespace renamed from root session x0001's library bundle
K4CubicTests (root.git branch x0001-cubiclib, commit d9813f5,
Submission/Lib/K4CubicTests/ConicConditioning.lean), not yet admitted to lib.
That file's own header follows.
-/
/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.ConicKernels

open MvPolynomial

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit

/-- A homogeneous linear polynomial with its three coefficients displayed. -/
noncomputable def linearPolynomial (a : Fin 3 → ℝ) : MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin 3, C (a i) * X i

private theorem coeff_monomial_triple_bound (f g h : Fin 3 → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ i, |f i| ≤ B) (hg : ∀ i, |g i| ≤ B) (hh : ∀ i, |h i| ≤ B)
    (m : Fin 3 →₀ ℕ) (i j k : Fin 3) :
    |((C (f i) * X i) * (C (g j) * X j) * (C (h k) * X k)).coeff m| ≤ B ^ 3 := by
  classical
  simp only [C_mul_X_eq_monomial, monomial_mul_monomial, coeff_monomial]
  split_ifs
  · simp only [abs_mul]
    calc
      |f i| * |g j| * |h k| ≤ B * B * B :=
        mul_le_mul (mul_le_mul (hf i) (hg j) (abs_nonneg _) hB) (hh k)
          (abs_nonneg _) (mul_nonneg hB hB)
      _ = _ := by ring
  · simp only [abs_zero]
    positivity

private theorem linearPolynomial_triple_expand (f g h : Fin 3 → ℝ) :
    linearPolynomial f * linearPolynomial g * linearPolynomial h =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        (C (f i) * X i) * (C (g j) * X j) * (C (h k) * X k) := by
  unfold linearPolynomial
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finset.sum_mul_sum _ _ _ _

private theorem abs_sum_three_le (f : Fin 3 → ℝ) (B : ℝ) (hf : ∀ i, |f i| ≤ B) :
    |∑ i, f i| ≤ 3 * B := by
  calc
    |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, B := Finset.sum_le_sum fun i _ => hf i
    _ = _ := by simp

private theorem abs_sum_three_cubed_le (f : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (B : ℝ) (hf : ∀ i j k, |f i j k| ≤ B) :
    |∑ i, ∑ j, ∑ k, f i j k| ≤ 27 * B := by
  have hinner (i j : Fin 3) : |∑ k, f i j k| ≤ 3 * B :=
    abs_sum_three_le (f i j) B (hf i j)
  have hmid (i : Fin 3) : |∑ j, ∑ k, f i j k| ≤ 3 * (3 * B) :=
    abs_sum_three_le (fun j => ∑ k, f i j k) (3 * B) (hinner i)
  convert abs_sum_three_le (fun i => ∑ j, ∑ k, f i j k) (3 * (3 * B)) hmid using 1 <;> ring

/-- A coefficient bound for a product of three linear polynomials. -/
theorem coeff_triple_linear_le (f g h : Fin 3 → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ i, |f i| ≤ B) (hg : ∀ i, |g i| ≤ B) (hh : ∀ i, |h i| ≤ B)
    (m : Fin 3 →₀ ℕ) :
    |(linearPolynomial f * linearPolynomial g * linearPolynomial h).coeff m| ≤ 27 * B ^ 3 := by
  classical
  rw [linearPolynomial_triple_expand]
  simp only [coeff_sum]
  exact abs_sum_three_cubed_le _ (B ^ 3) (coeff_monomial_triple_bound f g h B hB hf hg hh m)

/-- Coordinates of the joining-line polynomial. -/
def joiningCoefficients (u v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

theorem joiningLine_eq_linearPolynomial (u v : Fin 3 → ℝ) :
    joiningLine u v = linearPolynomial (joiningCoefficients u v) := by
  simp [joiningLine, linearPolynomial, joiningCoefficients, Fin.sum_univ_succ] <;> ring

theorem joiningCoefficients_le (u v : Fin 3 → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hu : ∀ i, |u i| ≤ A) (hv : ∀ i, |v i| ≤ A) :
    ∀ i, |joiningCoefficients u v i| ≤ 2 * A ^ 2 := by
  have habs (i j k l : Fin 3) : |u i * v j - u k * v l| ≤ 2 * A ^ 2 := by
    calc
      |u i * v j - u k * v l| ≤ |u i * v j| + |u k * v l| := abs_sub _ _
      _ = |u i| * |v j| + |u k| * |v l| := by rw [abs_mul, abs_mul]
      _ ≤ A * A + A * A := add_le_add
        (mul_le_mul (hu i) (hv j) (abs_nonneg _) hA)
        (mul_le_mul (hu k) (hv l) (abs_nonneg _) hA)
      _ = _ := by ring
  intro i
  fin_cases i
  · exact habs 1 2 2 1
  · exact habs 2 0 0 2
  · exact habs 0 1 1 0

theorem coeff_cubicSeparator_le (p : Fin 7 → Fin 3 → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hp : ∀ i j, |p i j| ≤ A) (i : Fin 7) (m : Fin 3 →₀ ℕ) :
    |(cubicSeparator p i).coeff m| ≤ 216 * A ^ 6 := by
  simp only [cubicSeparator, joiningLine_eq_linearPolynomial]
  calc
    _ ≤ 27 * (2 * A ^ 2) ^ 3 := coeff_triple_linear_le _ _ _ _ (by positivity)
      (joiningCoefficients_le _ _ A hA (hp _) (hp _))
      (joiningCoefficients_le _ _ A hA (hp _) (hp _))
      (joiningCoefficients_le _ _ A hA (hp _) (hp _)) m
    _ = _ := by ring

theorem abs_eval_cubicSeparator_ge (p : Fin 7 → Fin 3 → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      κ ≤ |Matrix.det (Matrix.of ![p i, p j, p k])|) (i : Fin 7) :
    κ ^ 3 ≤ |MvPolynomial.eval (p i) (cubicSeparator p i)| := by
  have hpair (a b : Fin 6) (hab : a ≠ b) :
      κ ≤ |MvPolynomial.eval (p i) (joiningLine (p (i.succAbove a)) (p (i.succAbove b)))| := by
    rw [eval_joiningLine]
    exact hp _ _ _ (Fin.succAbove_right_injective.ne hab) (Fin.succAbove_ne _ _) (Fin.succAbove_ne _ _)
  simp only [cubicSeparator, map_mul, abs_mul]
  calc
    κ ^ 3 = κ * κ * κ := by ring
    _ ≤ _ := by
      gcongr
      · exact hpair 0 1 (by decide)
      · exact hpair 2 3 (by decide)
      · exact hpair 4 5 (by decide)

theorem coeff_cubicCardinalPolynomial_le (p : Fin 7 → Fin 3 → ℝ)
    (A κ : ℝ) (hA : 0 ≤ A) (hκ : 0 < κ)
    (hcoord : ∀ i j, |p i j| ≤ A)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      κ ≤ |Matrix.det (Matrix.of ![p i, p j, p k])|)
    (i : Fin 7) (m : Fin 3 →₀ ℕ) :
    |(cubicCardinalPolynomial p i).coeff m| ≤ 216 * A ^ 6 / κ ^ 3 := by
  have hdenom := abs_eval_cubicSeparator_ge p κ hκ hp i
  have hinv : |MvPolynomial.eval (p i) (cubicSeparator p i)|⁻¹ ≤ (κ ^ 3)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hκ 3) hdenom
  simp only [cubicCardinalPolynomial, coeff_C_mul, abs_mul, abs_inv]
  calc
    _ ≤ (κ ^ 3)⁻¹ * (216 * A ^ 6) := by
      gcongr
      exact coeff_cubicSeparator_le p A hA hcoord i m
    _ = _ := by ring

/-- Quantitative rank-three conic kernel estimate, with an explicit polynomial
loss. The norm here bounds every coefficient of the error polynomial. -/
theorem exists_cubic_conic_approximation (p : Fin 7 → Fin 3 → ℝ)
    (A κ ε : ℝ) (hA : 0 ≤ A) (hκ : 0 < κ) (hε : 0 ≤ ε)
    (hcoord : ∀ i j, |p i j| ≤ A)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      κ ≤ |Matrix.det (Matrix.of ![p i, p j, p k])|)
    (q : MvPolynomial (Fin 3) ℝ) (hq : q.IsHomogeneous 2) (hne : q ≠ 0)
    (hqzero : ∀ i, MvPolynomial.eval (p i) q = 0)
    (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 3)
    (hFsmall : ∀ i, |MvPolynomial.eval (p i) F| ≤ ε) :
    ∃ L : MvPolynomial (Fin 3) ℝ, L.IsHomogeneous 1 ∧
      ∀ m : Fin 3 →₀ ℕ, |(F - q * L).coeff m| ≤ 1512 * A ^ 6 / κ ^ 3 * ε := by
  classical
  have hdet : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      Matrix.det (Matrix.of ![p i, p j, p k]) ≠ 0 := by
    intro i j k hij hik hjk
    exact abs_pos.mp (hκ.trans_le (hp i j k hij hik hjk))
  let R : MvPolynomial (Fin 3) ℝ :=
    ∑ i : Fin 7, C (MvPolynomial.eval (p i) F) * cubicCardinalPolynomial p i
  have hR : R.IsHomogeneous 3 := IsHomogeneous.sum _ _ _ fun i _ =>
    (cubicCardinalPolynomial_isHomogeneous p i).C_mul _
  have hRvalue (j : Fin 7) : MvPolynomial.eval (p j) R = MvPolynomial.eval (p j) F := by
    simp [R, eval_cubicCardinalPolynomial p hdet]
  have hzero (j : Fin 7) : MvPolynomial.eval (p j) (F - R) = 0 := by
    simp [hRvalue j]
  obtain ⟨L, hL, hFL⟩ := cubic_vanishing_eq_conic_mul_linear p hdet q hq hne hqzero
    (F - R) (hF.sub hR) hzero
  refine ⟨L, hL, ?_⟩
  have hdiff : F - q * L = R := by rw [← hFL]; ring
  intro m
  rw [hdiff]
  simp only [R, coeff_sum, coeff_C_mul]
  calc
    |∑ i : Fin 7, MvPolynomial.eval (p i) F * (cubicCardinalPolynomial p i).coeff m| ≤
        ∑ i : Fin 7, |MvPolynomial.eval (p i) F * (cubicCardinalPolynomial p i).coeff m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 7, ε * (216 * A ^ 6 / κ ^ 3) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul (hFsmall i) (coeff_cubicCardinalPolynomial_le p A κ hA hκ hcoord hp i m)
        (abs_nonneg _) hε
    _ = _ := by simp; ring

end Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit
