import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.ConditioningPowers
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Kit.PolynomialPerturbation

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition

open MvPolynomial

/-- Cubic tests transfer to a nearby exact conic with the same coordinate loss
as the quartic and quintic tests. -/
theorem exists_cubic_approximation_near_conic
    (p p' : Fin 7 → Fin 3 → ℝ) (A M Δ ε : ℝ) (hA : 2 ≤ A)
    (hM : 0 ≤ M) (hΔ : 0 ≤ Δ) (hε : 0 ≤ ε)
    (hcoord : ∀ i j, |p i j| ≤ A) (hcoord' : ∀ i j, |p' i j| ≤ A)
    (hdiff : ∀ i j, |p' i j - p i j| ≤ Δ)
    (hp : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
      A⁻¹ ≤ |Matrix.det (Matrix.of ![p' i, p' j, p' k])|)
    (q : MvPolynomial (Fin 3) ℝ) (hq : q.IsHomogeneous 2) (hqne : q ≠ 0)
    (hqzero : ∀ i, eval (p' i) q = 0)
    (F : MvPolynomial (Fin 3) ℝ) (hF : F.IsHomogeneous 3)
    (hcoeff : ∀ m, |F.coeff m| ≤ M)
    (hsmall : ∀ i, |eval (p i) F| ≤ ε) :
    ∃ P : MvPolynomial (Fin 3) ℝ, P.IsHomogeneous 1 ∧
      ∀ m : Fin 3 →₀ ℕ, |(F - q * P).coeff m| ≤
        A ^ 109 * (ε + 81 * A ^ 2 * M * Δ) := by
  have hnew (i : Fin 7) : |eval (p' i) F| ≤ ε + 81 * A ^ 2 * M * Δ := by
    convert Kit.homogeneous_eval_test_transfer F 2 hF A M Δ ε (by linarith) hM hΔ hcoeff
      (p i) (p' i) (hcoord i) (hcoord' i) (hdiff i) (hsmall i) using 1 <;> ring
  exact Kit.exists_cubic_conic_approximation_power_bound p' A _ hA (by positivity)
    hcoord' hp q hq hqne hqzero F hF hnew

end Submission.Obl.k4_approximate_conic_taylor_decomposition
