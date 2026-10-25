/-
Copied with the namespace renamed from o144 (k4_seven_direction_local_degree_restoration),
branch x0492, commit 9cac1f6, file Submission/Obl/k4_seven_direction_local_degree_restoration/Kit/ConicTestPerturbation.lean.
That file's own header follows.
-/
/-
Copied with the namespace renamed from root session x0001's library bundle
K4CubicTests (root.git branch x0001-cubiclib, commit d9813f5,
Submission/Lib/K4CubicTests/ConicTestPerturbation.lean), not yet admitted to lib.
That file's own header follows.
-/
/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.PolynomialPerturbation
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.ConditioningPowers

open MvPolynomial

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit

/-- Transfer all first-partial tests of a quartic to a nearby exact conic,
then apply the quantitative conic kernel theorem. -/
theorem exists_quartic_approximation_near_conic
    (p p' : Fin 7 → Fin 3 → ℝ) (A M Δ ε : ℝ) (hA : 2 ≤ A)
    (hM : 0 ≤ M) (hΔ : 0 ≤ Δ) (hε : 0 ≤ ε) (d : ℕ)
    (hcoord : ∀ i j, |p i j| ≤ A) (hcoord' : ∀ i j, |p' i j| ≤ A)
    (hdiff : ∀ i j, |p' i j - p i j| ≤ Δ)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      A⁻¹ ≤ |Matrix.det (Matrix.of ![p' i, p' j, p' k])|)
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQsym : Q.IsSymm)
    (hQ : ∀ i j, |Q i j| ≤ A ^ d) (hdet : (A ^ d)⁻¹ ≤ |Q.det|)
    (hqzero : ∀ i, MvPolynomial.eval (p' i) (matrixQuadratic Q) = 0)
    (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 4)
    (hcoeff : ∀ m, |F.coeff m| ≤ M)
    (hsmall : ∀ i j, |MvPolynomial.eval (p i) (pderiv j F)| ≤ ε) :
    ∃ r : ℝ, ∀ m : Fin 3 →₀ ℕ,
      |(F - C r * (matrixQuadratic Q) ^ 2).coeff m| ≤
        A ^ (137 + 8 * d) * (ε + 324 * A ^ 2 * M * Δ) := by
  have hA0 : 0 ≤ A := by linarith
  have hdcoeff (j : Fin 3) (m : Fin 3 →₀ ℕ) : |(pderiv j F).coeff m| ≤ 4 * M :=
    coeff_pderiv_abs_le_of_totalDegree F 4 hF.totalDegree_le M hM hcoeff j m
  have hnew (i : Fin 7) (j : Fin 3) :
      |MvPolynomial.eval (p' i) (pderiv j F)| ≤ ε + 324 * A ^ 2 * M * Δ := by
    convert homogeneous_eval_test_transfer (pderiv j F) 2 (by simpa using hF.pderiv)
      A (4 * M) Δ ε hA0 (by positivity) hΔ (hdcoeff j) (p i) (p' i)
      (hcoord i) (hcoord' i) (hdiff i) (hsmall i j) using 1 <;> ring
  exact exists_quartic_approximation_power_bound p' A _ hA (by positivity) d hcoord' hp Q hQsym hQ hdet
    hqzero F hF hnew

/-- Transfer all second-partial tests of a quintic to a nearby exact conic,
then apply quantitative injectivity of the conic tests. -/
theorem quintic_coefficients_le_near_conic_tests
    (p p' : Fin 7 → Fin 3 → ℝ) (A M Δ ε : ℝ) (hA : 2 ≤ A)
    (hM : 0 ≤ M) (hΔ : 0 ≤ Δ) (hε : 0 ≤ ε) (d : ℕ)
    (hcoord : ∀ i j, |p i j| ≤ A) (hcoord' : ∀ i j, |p' i j| ≤ A)
    (hdiff : ∀ i j, |p' i j - p i j| ≤ Δ)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      A⁻¹ ≤ |Matrix.det (Matrix.of ![p' i, p' j, p' k])|)
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQsym : Q.IsSymm)
    (hQ : ∀ i j, |Q i j| ≤ A ^ d) (hdet : (A ^ d)⁻¹ ≤ |Q.det|)
    (hqzero : ∀ i, MvPolynomial.eval (p' i) (matrixQuadratic Q) = 0)
    (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 5)
    (hcoeff : ∀ m, |F.coeff m| ≤ M)
    (hsmall : ∀ i j k, |MvPolynomial.eval (p i) (pderiv j (pderiv k F))| ≤ ε) :
    ∀ m : Fin 3 →₀ ℕ, |F.coeff m| ≤
      A ^ (137 + 16 * d) * (ε + 1620 * A ^ 2 * M * Δ) := by
  have hA0 : 0 ≤ A := by linarith
  have hdhom (k : Fin 3) : (pderiv k F).IsHomogeneous 4 := by simpa using hF.pderiv
  have hdcoeff (k : Fin 3) (m : Fin 3 →₀ ℕ) : |(pderiv k F).coeff m| ≤ 5 * M :=
    coeff_pderiv_abs_le_of_totalDegree F 5 hF.totalDegree_le M hM hcoeff k m
  have hddcoeff (j k : Fin 3) (m : Fin 3 →₀ ℕ) : |(pderiv j (pderiv k F)).coeff m| ≤ 20 * M := by
    convert coeff_pderiv_abs_le_of_totalDegree (pderiv k F) 4 (hdhom k).totalDegree_le
      (5 * M) (by positivity) (hdcoeff k) j m using 1 <;> ring
  have hnew (i : Fin 7) (j k : Fin 3) :
      |MvPolynomial.eval (p' i) (pderiv j (pderiv k F))| ≤ ε + 1620 * A ^ 2 * M * Δ := by
    convert homogeneous_eval_test_transfer (pderiv j (pderiv k F)) 2 (by simpa using (hdhom k).pderiv)
      A (20 * M) Δ ε hA0 (by positivity) hΔ (hddcoeff j k) (p i) (p' i)
      (hcoord i) (hcoord' i) (hdiff i) (hsmall i j k) using 1 <;> ring
  exact quintic_coefficients_le_power_bound p' A _ hA (by positivity) d hcoord' hp Q hQsym hQ hdet
    hqzero F hF hnew

end Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit
