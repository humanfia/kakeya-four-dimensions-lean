import Submission.Obl.k4_stable_native_signal_oscillation.ComplexPolynomial
import Submission.Obl.k4_algebraic_sheet_remez

namespace Submission.Obl.k4_stable_native_signal_oscillation
open MvPolynomial Set Metric MeasureTheory

/-- The accepted algebraic-sheet Remez theorem applies in particular to real polynomials. -/
lemma exists_polynomial_remez_half_ball (D : ℕ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
    ∀ (E : Set (EuclideanSpace ℝ (Fin 3))) (θ V : ℝ),
      MeasurableSet E → E ⊆ closedBall 0 (1 / 2) →
      0 < θ → θ ≤ 1 → 0 ≤ V →
      ENNReal.ofReal θ * volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)) ≤ volume E →
      (∀ x ∈ E, |eval (fun i => x i) P| ≤ V) →
      ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 →
        |eval (fun i => x i) P| ≤ C * θ ^ (-C) * V := by
  obtain ⟨C, hC, hremez⟩ := Submission.k4_algebraic_sheet_remez 3 (max 1 D)
  refine ⟨C, hC, ?_⟩
  intro P hP E θ V hE hEsub hθ hθ1 hV hmass hbound x hx
  let Q := P.map (algebraMap ℝ ℂ)
  let f : EuclideanSpace ℂ (Fin 3) → ℂ := fun z => eval (fun i => z i) Q
  have hrel := polynomial_hasSheetRelation Q ((complexification_degree P).trans hP)
  obtain ⟨R, hR, hRD, hroot⟩ := hrel
  have hreal : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u‖ ≤ 1 →
      (f (WithLp.toLp 2 (fun j => (u j : ℂ)))).im = 0 := by
    intro u hu
    simp only [f, Q, eval_complexification, Complex.ofReal_im]
  have hbound' : ∀ u ∈ E, ‖f (WithLp.toLp 2 (fun j => (u j : ℂ)))‖ ≤ V := by
    intro u hu
    simpa only [f, Q, eval_complexification, Complex.norm_real, Real.norm_eq_abs] using hbound u hu
  have h := hremez R f hR hRD (differentiable_polynomial Q).differentiableOn
    hroot hreal E θ V hE hEsub hθ hθ1 hV hmass hbound' x hx
  simpa only [f, Q, eval_complexification, Complex.norm_real, Real.norm_eq_abs] using h

end Submission.Obl.k4_stable_native_signal_oscillation
