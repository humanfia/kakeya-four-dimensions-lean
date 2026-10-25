import Mathlib
import ChallengeDeps
import Submission.Obl.k4_polynomial_variation_tube.Cylinder
import Submission.Obl.k4_polynomial_variation_tube.LineVariation
set_option linter.unusedVariables false

/-!
# `Submission.k4_polynomial_variation_tube`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_polynomial_variation_tube`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_polynomial_variation_tube/`
belong to this obligation.

The proof bounds the overlap of the lattice balls, rotates the line to the first
coordinate axis, and applies the polynomial line-variation bound on each fiber.
-/

theorem Submission.k4_polynomial_variation_tube : ∀ n : ℕ, 2 ≤ n → ∃ C : ℝ, 0 < C ∧ (∀ (p : MvPolynomial (Fin n) ℝ) (c v : EuclideanSpace ℝ (Fin n)), MeasureTheory.IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => ‖(fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => Real.arctan (MvPolynomial.eval (fun j => y j) p)) x) v‖) (Metric.ball c 1) MeasureTheory.volume) ∧ ∀ (m : ℕ) (z : Fin m → Fin n → ℤ), Function.Injective z → ∀ (p : MvPolynomial (Fin n) ℝ) (a e : EuclideanSpace ℝ (Fin n)), ‖e‖ = 1 → (∑ q : Fin m, (Metric.thickening (3 : ℝ) (Set.range fun t : ℝ => a + t • e)).indicator (fun _ => (1 : ℝ)) (WithLp.toLp 2 (fun j : Fin n => (z q j : ℝ))) * (MeasureTheory.integral (MeasureTheory.volume.restrict (Metric.ball (WithLp.toLp 2 (fun j : Fin n => (z q j : ℝ))) 1)) (fun x : EuclideanSpace ℝ (Fin n) => ‖(fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => Real.arctan (MvPolynomial.eval (fun j => y j) p)) x) e‖))) ≤ C * (p.totalDegree : ℝ) := by
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨C, hC, hbound⟩ := Submission.Obl.k4_polynomial_variation_tube.exists_continuous_tube_bound n
    refine ⟨C * Real.pi, mul_pos hC Real.pi_pos, ?_, ?_⟩
    · intro p c v
      exact Submission.Obl.k4_polynomial_variation_tube.integrableOn_directional_variation p c v
    · intro m z hz p a e he
      let f : EuclideanSpace ℝ (Fin (n+1)) → ℝ := fun x =>
        ‖(fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (n+1)) =>
          Real.arctan (MvPolynomial.eval (fun j => y j) p)) x) e‖
      have hf : Continuous f :=
        Submission.Obl.k4_polynomial_variation_tube.continuous_directional_variation p e
      have hline : ∀ (b : EuclideanSpace ℝ (Fin (n+1))) (s t : ℝ), s ≤ t →
          (MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Icc s t))
            (fun u => f (b + u • e))) ≤ Real.pi * p.totalDegree := by
        intro b s t _
        simpa only [f, Submission.Obl.k4_polynomial_variation_tube.line_deriv_eq_fderiv] using
          Submission.Obl.k4_polynomial_variation_tube.line_variation_Icc p b e s t
      have h := hbound m
        (fun q => WithLp.toLp 2 (fun j => (z q j : ℝ)))
        (fun q r hqr => Submission.Obl.k4_polynomial_variation_tube.lattice_separated z hz hqr)
        a e he f hf (fun x => norm_nonneg _) (Real.pi * p.totalDegree) hline
      simpa only [f, mul_assoc] using h
