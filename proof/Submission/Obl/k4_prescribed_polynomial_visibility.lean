import Mathlib
import ChallengeDeps
import Submission.Obl.k4_prescribed_polynomial_visibility.OneStep
import Submission.Obl.k4_prescribed_polynomial_visibility.Iteration
set_option linter.unusedVariables false

/-!
# `Submission.k4_prescribed_polynomial_visibility`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_prescribed_polynomial_visibility`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_prescribed_polynomial_visibility/`
belong to this obligation.
-/

open Submission.Obl.k4_prescribed_polynomial_visibility

theorem Submission.k4_prescribed_polynomial_visibility : ∀ n : ℕ, 3 ≤ n → n ≤ 4 → ∃ L : ℝ, 0 < L ∧ ∀ (m : ℕ) (z : Fin m → Fin n → ℤ), Function.Injective z → ∀ M : Fin m → ℝ, (∀ q : Fin m, 0 ≤ M q) → (∑ q : Fin m, M q) = 1 → ∃ D : ℝ, (m : ℝ) + 1 ≤ D ∧ ∃ (r : ℕ) (p : Fin r → MvPolynomial (Fin n) ℝ) (w : Fin r → ℝ) (V : Fin m → Seminorm ℝ (EuclideanSpace ℝ (Fin n))), (∀ q : Fin m, Continuous (V q)) ∧ (∀ h : Fin r, 0 ≤ w h) ∧ (∑ h : Fin r, w h) = 1 ∧ (∀ h : Fin r, ((p h).totalDegree : ℝ) ≤ L * D) ∧ (∀ (q : Fin m) (v : EuclideanSpace ℝ (Fin n)), V q v = ‖v‖ + ∑ h : Fin r, w h * (MeasureTheory.integral (MeasureTheory.volume.restrict (Metric.ball (WithLp.toLp 2 (fun j : Fin n => (z q j : ℝ))) 1)) (fun x : EuclideanSpace ℝ (Fin n) => ‖(fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => Real.arctan (MvPolynomial.eval (fun j => y j) (p h))) x) v‖))) ∧ (∀ (q : Fin m) (v : EuclideanSpace ℝ (Fin n)), ‖v‖ ≤ V q v) ∧ ∀ q : Fin m, 0 < M q → MeasureTheory.volume {v : EuclideanSpace ℝ (Fin n) | V q v ≤ 1} ≤ ENNReal.ofReal ((D ^ n * M q)⁻¹) := by
  intro n hn _hn4
  obtain ⟨C, hC, hstep⟩ := exists_polynomial_improvement n (by omega)
  have hOracle : ImprovementOracle n C := by
    intro m c V _hcont hV T hT M hM hsum
    obtain ⟨p, hp, himprove⟩ := hstep m c M hM hsum T hT V hV
    refine ⟨p, hp, ?_⟩
    intro q hq hlarge
    obtain ⟨v, hv, hSv⟩ := himprove q hq hlarge
    refine ⟨v, hv, ?_⟩
    simpa only [pow_mul, show (2 : ℝ) ^ 3 = 8 by norm_num] using hSv
  obtain ⟨L, hL, hensemble⟩ := prescribed_ensemble_of_improvement n C hC hOracle
  refine ⟨L, hL, ?_⟩
  intro m z _hz M hM hsum
  let c : Fin m → EuclideanSpace ℝ (Fin n) :=
    fun q => WithLp.toLp 2 (fun j => (z q j : ℝ))
  obtain ⟨D, hD, hens⟩ := hensemble m c M hM hsum
  obtain ⟨r, p, w, hw, hwsum, hpdeg, hvolume⟩ := hens
  refine ⟨D, hD, r, p, w, (fun q => ensemble p w hw (c q)), ?_, hw,
    hwsum, hpdeg, ?_, ?_, ?_⟩
  · intro q
    exact continuous_ensemble p w hw (c q)
  · intro q v
    exact ensemble_apply p w hw (c q) v
  · intro q v
    exact norm_le_ensemble p w hw (c q) v
  · exact hvolume
