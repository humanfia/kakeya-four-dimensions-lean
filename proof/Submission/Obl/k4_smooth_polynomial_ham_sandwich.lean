import Mathlib
import ChallengeDeps
import Submission.Obl.k4_smooth_polynomial_ham_sandwich.Bisect
import Submission.Obl.k4_smooth_polynomial_ham_sandwich.Smoothing
set_option linter.unusedVariables false

/-!
# `Submission.k4_smooth_polynomial_ham_sandwich`

Apply polynomial ham sandwich to the restricted volume measures, then scale the
resulting nonzero polynomial. Its zero set is null, so dominated convergence for
the arctangent supplies one scale satisfying all the integral bounds.
-/

open MeasureTheory Submission.Obl.k4_smooth_polynomial_ham_sandwich in
theorem Submission.k4_smooth_polynomial_ham_sandwich : ∀ n : ℕ, 1 ≤ n → ∀ T : ℝ, 1 ≤ T → ∀ (k : ℕ) (Q : Fin k → Set (EuclideanSpace ℝ (Fin n))), (k : ℝ) ≤ T ^ n → (∀ h : Fin k, IsCompact (Q h) ∧ 0 < MeasureTheory.volume (Q h)) → ∃ p : MvPolynomial (Fin n) ℝ, (p.totalDegree : ℝ) ≤ (n : ℝ) * T ∧ ∀ h : Fin k, |MeasureTheory.integral (MeasureTheory.volume.restrict (Q h)) (fun x : EuclideanSpace ℝ (Fin n) => Real.arctan (MvPolynomial.eval (fun j => x j) p))| ≤ (MeasureTheory.volume (Q h)).toReal / 2 ∧ (MeasureTheory.volume (Q h)).toReal ≤ MeasureTheory.integral (MeasureTheory.volume.restrict (Q h)) (fun x : EuclideanSpace ℝ (Fin n) => |Real.arctan (MvPolynomial.eval (fun j => x j) p)|) := by
  intro n hn T hT k Q hk hQ
  let μ : Fin k → Measure (EuclideanSpace ℝ (Fin n)) := fun i => volume.restrict (Q i)
  have : ∀ i, IsFiniteMeasure (μ i) := fun i =>
    ⟨by simpa only [μ, Measure.restrict_apply_univ] using (hQ i).1.measure_lt_top⟩
  obtain ⟨p, hp, hdeg, hbisect⟩ := exists_bisecting_poly_deg n hn T hT hk μ
  have hpos : ∀ i, 0 < μ i Set.univ := by
    intro i
    simpa only [μ, Measure.restrict_apply_univ] using (hQ i).2
  have hzero : ∀ i, μ i {x | MvPolynomial.eval (fun j => x j) p = 0} = 0 := by
    intro i
    exact le_antisymm ((Measure.restrict_apply_le (Q i) _).trans_eq
      (volume_zeroSet_eucl p hp)) zero_le
  obtain ⟨R, hR, hscale⟩ := exists_arctan_scale μ hpos _ (measurable_evalE p) hzero hbisect
  refine ⟨R • p, (Nat.cast_le.mpr (MvPolynomial.totalDegree_smul_le R p)).trans hdeg, ?_⟩
  intro i
  simpa only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
    μ, Measure.restrict_apply_univ] using hscale i
