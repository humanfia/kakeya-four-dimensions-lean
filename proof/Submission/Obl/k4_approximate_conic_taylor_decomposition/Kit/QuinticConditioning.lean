/-
Copied with the namespace renamed from o144 (k4_seven_direction_local_degree_restoration),
branch x0492, commit 9cac1f6, file Submission/Obl/k4_seven_direction_local_degree_restoration/Kit/QuinticConditioning.lean.
That file's own header follows.
-/
/-
Copied with the namespace renamed from root session x0001's library bundle
K4CubicTests (root.git branch x0001-cubiclib, commit d9813f5,
Submission/Lib/K4CubicTests/QuinticConditioning.lean), not yet admitted to lib.
That file's own header follows.
-/
/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.QuarticConditioning
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.QuadraticDivision

open MvPolynomial

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit

noncomputable def quinticConicError (A κ Qbound R S T U V ε : ℝ) : ℝ :=
  3 * (648 * T ^ 2 * quarticConicError A κ Qbound R S T U V ε * (18 * Qbound * U) +
    quarticConicError A κ Qbound R S T U V ε)

/-- Explicit injectivity conditioning of the quintic conic tests. -/
theorem quintic_coefficients_le_of_conic_tests
    (p : Fin 7 → Fin 3 → ℝ) (A κ Qbound R S T U V ε : ℝ)
    (hA : 0 ≤ A) (hκ : 0 < κ) (hQbound : 0 ≤ Qbound)
    (hR : 1 ≤ R) (hS : 0 ≤ S) (hT : 0 ≤ T) (hU : 0 ≤ U) (hV : 0 ≤ V) (hε : 0 ≤ ε)
    (hcoord : ∀ i j, |p i j| ≤ A)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      κ ≤ |Matrix.det (Matrix.of ![p i, p j, p k])|)
    (q : MvPolynomial (Fin 3) ℝ) (hq : q.IsHomogeneous 2) (hne : q ≠ 0)
    (hqzero : ∀ i, MvPolynomial.eval (p i) q = 0)
    (hqcoeff : ∀ m, |q.coeff m| ≤ Qbound)
    (B P : Matrix (Fin 3) (Fin 3) ℝ) (hBsym : B.IsSymm)
    (hBdet : IsUnit B.det) (hPdet : IsUnit P.det)
    (hgrad : ∀ x : Fin 3 → ℝ, ∀ j, MvPolynomial.eval x (pderiv j q) = Matrix.mulVec B x j)
    (α : Fin 3 → ℝ) (hα : ∀ i, |α i| ≤ R) (hlow : ∀ i, 1 ≤ R * |α i|)
    (hPinv : ∀ i j, |P⁻¹ i j| ≤ S) (hBinv : ∀ i j, |B⁻¹ i j| ≤ T)
    (hB : ∀ i j, |B i j| ≤ U) (hP : ∀ i j, |P i j| ≤ V)
    (hframe : ∀ i : Fin 3, p (Fin.castLE (by decide : 3 ≤ 7) i) = fun l => P l i)
    (hextra : p 3 = Matrix.mulVec P α)
    (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 5)
    (hsmall : ∀ i j k, |MvPolynomial.eval (p i) (pderiv j (pderiv k F))| ≤ ε) :
    ∀ m : Fin 3 →₀ ℕ, |F.coeff m| ≤ quinticConicError A κ Qbound R S T U V ε := by
  classical
  let η := quarticConicError A κ Qbound R S T U V ε
  have hη : 0 ≤ η := by
    dsimp [η, quarticConicError, quarticParallelError, cubicConicError]
    positivity
  have hexists (k : Fin 3) : ∃ r : ℝ, ∀ m, |(pderiv k F - C r * q ^ 2).coeff m| ≤ η :=
    exists_quartic_conic_approximation p A κ Qbound R S T U V ε hA hκ hQbound hR hS hT hU hV hε
      hcoord hp q hq hne hqzero hqcoeff B P hBdet hPdet hgrad α hα hlow hPinv hBinv hB hP
      hframe hextra (pderiv k F) (by simpa using hF.pderiv) (fun i j => hsmall i j k)
  choose r hEc using hexists
  let E (k : Fin 3) := pderiv k F - C (r k) * q ^ 2
  have hEhom (k : Fin 3) : (E k).IsHomogeneous 4 := by
    dsimp [E]
    rw [pow_two]
    exact (hF.pderiv : (pderiv k F).IsHomogeneous 4).sub ((hq.mul hq).C_mul (r k))
  have hEcoeff (k : Fin 3) (m : Fin 3 →₀ ℕ) : |(E k).coeff m| ≤ η := hEc k m
  have hEdcoeff (j k : Fin 3) (m : Fin 3 →₀ ℕ) : |(pderiv j (E k)).coeff m| ≤ 4 * η :=
    coeff_pderiv_abs_le_of_totalDegree (E k) 4 (hEhom k).totalDegree_le η hη (hEcoeff k) j m
  have hqpoly (j : Fin 3) : pderiv j q = linearPolynomial (fun k => B j k) := by
    apply MvPolynomial.funext
    intro x
    simpa [linearPolynomial, Matrix.mulVec, dotProduct] using hgrad x j
  let a (j k : Fin 3) (i : Fin 3) := r j * B k i - r k * B j i
  have halinear (j k : Fin 3) : linearPolynomial (a j k) =
      C (r j) * pderiv k q - C (r k) * pderiv j q := by
    rw [hqpoly k, hqpoly j]
    simp only [linearPolynomial, a, Finset.mul_sum, ← Finset.sum_sub_distrib, map_sub, map_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hidentity (j k : Fin 3) : (2 : MvPolynomial (Fin 3) ℝ) * (q * linearPolynomial (a j k)) =
      pderiv j (E k) - pderiv k (E j) := by
    rw [halinear j k]
    dsimp [E]
    simp only [map_sub, pderiv_C_mul, pow_two, pderiv_mul, pderiv_C,
      zero_mul, mul_zero, zero_add, add_zero]
    rw [polynomial_pderiv_comm F j k]
    ring
  have hqacoeff (j k : Fin 3) (m : Fin 3 →₀ ℕ) :
      |(q * linearPolynomial (a j k)).coeff m| ≤ 4 * η := by
    have hid := congrArg (fun H : MvPolynomial (Fin 3) ℝ => H.coeff m) (hidentity j k)
    rw [show (2 : MvPolynomial (Fin 3) ℝ) = C (2 : ℝ) by rw [map_ofNat], coeff_C_mul] at hid
    have hdiff : |(pderiv j (E k) - pderiv k (E j)).coeff m| ≤ 8 * η := by
      change |(pderiv j (E k)).coeff m - (pderiv k (E j)).coeff m| ≤ 8 * η
      exact (abs_sub _ _).trans (by linarith [hEdcoeff j k m, hEdcoeff k j m])
    rw [← hid, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hdiff
    linarith
  have hacoeff (j k i : Fin 3) : |a j k i| ≤ 216 * T * η := by
    convert linear_coefficients_le_of_quadratic_product q hq B hBsym hBdet hqpoly
      (a j k) T (4 * η) hT (by positivity) hBinv (hqacoeff j k) i using 1 <;> ring
  have hr (j : Fin 3) : |r j| ≤ 648 * T ^ 2 * η := by
    let k : Fin 3 := j.succAbove (0 : Fin 2)
    have hkj : k ≠ j := Fin.succAbove_ne _ _
    have hrec : ∑ i : Fin 3, a j k i * B⁻¹ i k = r j := by
      calc
        _ = r j * (B * B⁻¹) k k - r k * (B * B⁻¹) j k := by
          simp only [a, Matrix.mul_apply, Fin.sum_univ_three]
          ring
        _ = _ := by rw [Matrix.mul_nonsing_inv B hBdet]; simp [Matrix.one_apply, hkj, Ne.symm hkj]
    have hterm (i : Fin 3) : |a j k i * B⁻¹ i k| ≤ (216 * T * η) * T := by
      rw [abs_mul]
      exact mul_le_mul (hacoeff j k i) (hBinv i k) (abs_nonneg _) (by positivity)
    calc
      |r j| = |∑ i : Fin 3, a j k i * B⁻¹ i k| := congrArg abs hrec.symm
      _ ≤ ∑ i : Fin 3, |a j k i * B⁻¹ i k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, (216 * T * η) * T := Finset.sum_le_sum fun i _ => hterm i
      _ = _ := by simp; ring
  have hq2hom : (q ^ 2).IsHomogeneous 4 := by simpa only [pow_two] using hq.mul hq
  have hq2deriv (j : Fin 3) : pderiv j (q ^ 2) =
      (2 : MvPolynomial (Fin 3) ℝ) * (q * linearPolynomial (fun k => B j k)) := by
    rw [pow_two, pderiv_mul, hqpoly j]
    ring
  have hq2dcoeff (j : Fin 3) (m : Fin 3 →₀ ℕ) : |(pderiv j (q ^ 2)).coeff m| ≤ 6 * Qbound * U := by
    rw [hq2deriv j, show (2 : MvPolynomial (Fin 3) ℝ) = C (2 : ℝ) by rw [map_ofNat],
      coeff_C_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hprod := coeff_mul_linearPolynomial_abs_le q (fun k => B j k) Qbound U
      hQbound hU hqcoeff (hB j) m
    nlinarith
  have hq2coeff (m : Fin 3 →₀ ℕ) : |(q ^ 2).coeff m| ≤ 18 * Qbound * U := by
    convert homogeneous_coeff_abs_le_of_pderiv (q ^ 2) 4 (by decide) hq2hom
      (6 * Qbound * U) (by positivity) hq2dcoeff m using 1 <;> ring
  have hFdeq (j : Fin 3) : pderiv j F = C (r j) * q ^ 2 + E j := by dsimp [E]; ring
  have hFdcoeff (j : Fin 3) (m : Fin 3 →₀ ℕ) :
      |(pderiv j F).coeff m| ≤ 648 * T ^ 2 * η * (18 * Qbound * U) + η := by
    rw [hFdeq j, MvPolynomial.coeff_add]
    apply (abs_add_le _ _).trans
    rw [coeff_C_mul, abs_mul]
    exact add_le_add (mul_le_mul (hr j) (hq2coeff m) (abs_nonneg _) (by positivity)) (hEcoeff j m)
  intro m
  change |F.coeff m| ≤ 3 * (648 * T ^ 2 * η * (18 * Qbound * U) + η)
  exact homogeneous_coeff_abs_le_of_pderiv F 5 (by decide) hF _ (by positivity) hFdcoeff m

end Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit
