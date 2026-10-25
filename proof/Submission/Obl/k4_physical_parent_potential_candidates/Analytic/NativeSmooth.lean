-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/NativeSmooth.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/NativeSmooth.lean.
-- Existing source attributions are preserved below.

-- Adapted from this LOT tree, o143, session x0487 (including x0491 contributions),
-- branch merged/o143/x0487, commit 36234c3602987ce26ddd4bced782149873fbaa4e.
-- Original file: Submission/Obl/k4_isotropic_discovery_of_local_restoration/NativeSmooth.lean
-- Earlier source attributions below are retained.
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.RationalSquareRoot
import Submission.Obl.k4_quadratic_sheet_continuation.Smooth

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial
open scoped ContDiff

theorem hidden_pderiv_liftBasePolynomial {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    pderiv (Fin.last n) (liftBasePolynomial P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [liftBasePolynomial]
  | add P Q hP hQ => simpa only [liftBasePolynomial, map_add, zero_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    have hP' : pderiv (Fin.last n) (rename Fin.castSucc P) = 0 := hP
    simp [liftBasePolynomial, hP']

/-- A native hidden quadratic, allowing arbitrary fixed degrees in the base. -/
def nativeQuadraticPolynomial {n : ℕ} (a : ℂ) (B C₀ : MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin (n + 1)) ℂ :=
  liftBasePolynomial C₀ + liftBasePolynomial B * X (Fin.last n) + C a * X (Fin.last n) ^ 2

theorem eval_nativeQuadraticPolynomial {n : ℕ} (a : ℂ)
    (B C₀ : MvPolynomial (Fin n) ℂ) (z : Fin n → ℂ) (w : ℂ) :
    eval (Fin.snoc z w) (nativeQuadraticPolynomial a B C₀) =
      eval z C₀ + eval z B * w + a * w ^ 2 := by
  simp [nativeQuadraticPolynomial, eval_liftBasePolynomial]

theorem pderiv_nativeQuadraticPolynomial {n : ℕ} (a : ℂ)
    (B C₀ : MvPolynomial (Fin n) ℂ) :
    pderiv (Fin.last n) (nativeQuadraticPolynomial a B C₀) =
      liftBasePolynomial B + C (2 * a) * X (Fin.last n) := by
  simp [nativeQuadraticPolynomial, pow_two, hidden_pderiv_liftBasePolynomial, map_ofNat]
  ring

/-- The accepted smooth implicit-root theorem upgrades a continuous simple
native branch directly to any complex smoothness order. This avoids a
several-variable holomorphic-to-smooth theorem. -/
theorem contDiffOn_simple_native_quadratic_branch {n : ℕ}
    (a : ℂ) (B C₀ : MvPolynomial (Fin n) ℂ)
    {Ω : Set (EuclideanSpace ℂ (Fin n))} (hΩ : IsOpen Ω)
    {F : EuclideanSpace ℂ (Fin n) → ℂ} (hF : ContinuousOn F Ω)
    (hroot : ∀ z ∈ Ω, eval (fun i => z i) C₀ +
      eval (fun i => z i) B * F z + a * (F z) ^ 2 = 0)
    (hsimple : ∀ z ∈ Ω, eval (fun i => z i) B + 2 * a * F z ≠ 0)
    (k : ℕ∞ω) : ContDiffOn ℂ k F Ω := by
  apply k4_quadratic_sheet_continuation.contDiffOn_simple_polynomial_root hΩ
    (nativeQuadraticPolynomial a B C₀) hF ?_ ?_ k
  · intro z hz
    simpa only [eval_nativeQuadraticPolynomial] using hroot z hz
  · intro z hz
    simpa only [pderiv_nativeQuadraticPolynomial, map_add, map_mul,
      eval_liftBasePolynomial, eval_C, eval_X, Fin.snoc_last] using hsimple z hz

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
