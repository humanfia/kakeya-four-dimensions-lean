import Mathlib
import ChallengeDeps
import Submission.Obl.k4_stable_native_signal_oscillation.Closure
import Submission.Obl.k4_stable_native_signal_oscillation.ExactRoot
set_option linter.unusedVariables false

/-!
# `Submission.k4_stable_native_signal_oscillation`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_stable_native_signal_oscillation`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_stable_native_signal_oscillation/`
belong to this obligation.

The proof: `Closure.of_exact_root_partition` (high curvature by the affine center and
polynomial control; low curvature by lifting each point to the exact simple root of the
hidden quadratic) reduces the statement to the exact-root partition, which
`ExactRoot.er_partition` proves from the fixed-degree polynomial control
`PolynomialControl.exists_polynomial_control` (Remez through the accepted
`Submission.k4_algebraic_sheet_remez`).
-/

theorem Submission.k4_stable_native_signal_oscillation : ((fun (V₀:Prop) => V₀) (∀ A:ℕ,∃ C:ℕ,1 ≤ C∧∀ (K a:ℝ) (P S:MvPolynomial (Fin 4) ℝ) (μ:MeasureTheory.Measure (EuclideanSpace ℝ (Fin 4))),2 ≤ K→ 0 < a→ a ≤ 1→ P.totalDegree ≤ 2→ S.totalDegree ≤ 2→ MeasureTheory.IsProbabilityMeasure μ→ (fun base:EuclideanSpace ℝ (Fin 4)→ EuclideanSpace ℝ (Fin 3) => MeasureTheory.Measure.map base μ ≤ ENNReal.ofReal K • MeasureTheory.volume→ (∀ᵐ p ∂μ,‖base p‖ ≤ K∧ |MvPolynomial.eval (fun i => p i) P| ≤ K * a∧K⁻¹ ≤ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) P)|∧ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) P)| ≤ K∧ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) P))| ≤ K / a∧ |MvPolynomial.eval (fun i => p i) S| ≤ K∧ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) S)| ≤ K∧ |MvPolynomial.eval (fun i => p i) (MvPolynomial.pderiv (3:Fin 4) (MvPolynomial.pderiv (3:Fin 4) S))| ≤ K)→ ∃ (n:ℕ) (E:Fin n→ Set (EuclideanSpace ℝ (Fin 4))),(n:ℝ) ≤ K ^ C∧(∀ i,MeasurableSet (E i))∧(∀ i j,i ≠ j→ Disjoint (E i) (E j))∧μ (⋃ i,E i)ᶜ ≤ ENNReal.ofReal ((K ^ A)⁻¹)∧∀ i p,p ∈ E i→ ∀ q,q ∈ E i→ |MvPolynomial.eval (fun j => p j) S - MvPolynomial.eval (fun j => q j) S| ≤ K ^ C * (a + ‖base p - base q‖)) (fun p => WithLp.toLp 2 ![p 0,p 1,p 2]))) :=
  Submission.Obl.k4_stable_native_signal_oscillation.of_exact_root_partition
    (fun A => Submission.Obl.k4_stable_native_signal_oscillation.er_partition
      (fun D m => Submission.Obl.k4_stable_native_signal_oscillation.exists_polynomial_control D m) A)
