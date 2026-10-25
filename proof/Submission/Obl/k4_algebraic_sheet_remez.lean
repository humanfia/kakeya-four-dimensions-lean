import Mathlib
import ChallengeDeps
import Submission.Obl.k4_algebraic_sheet_remez.Proof
set_option linter.unusedVariables false

/-!
# `Submission.k4_algebraic_sheet_remez`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_algebraic_sheet_remez`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_algebraic_sheet_remez/`
belong to this obligation.
-/

theorem Submission.k4_algebraic_sheet_remez : ∀ n D : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : MvPolynomial (Fin (n + 1)) ℂ) (f : EuclideanSpace ℂ (Fin n) → ℂ), P ≠ 0 → P.totalDegree ≤ D → DifferentiableOn ℂ f (Metric.ball 0 4) → (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin n)) 4, MvPolynomial.eval (Fin.snoc (fun j : Fin n => z j) (f z)) P = 0) → (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → (f (WithLp.toLp 2 (fun j => (x j : ℂ)))).im = 0) → ∀ (E : Set (EuclideanSpace ℝ (Fin n))) (θ V : ℝ), MeasurableSet E → E ⊆ Metric.closedBall 0 (1 / 2) → 0 < θ → θ ≤ 1 → 0 ≤ V → ENNReal.ofReal θ * MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) ≤ MeasureTheory.volume E → (∀ x ∈ E, ‖f (WithLp.toLp 2 (fun j => (x j : ℂ)))‖ ≤ V) → ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 / 2 → ‖f (WithLp.toLp 2 (fun j => (x j : ℂ)))‖ ≤ C * θ ^ (-C) * V := by
  intro n D
  by_cases hn : n = 0
  · subst n
    refine ⟨1, le_rfl, ?_⟩
    intro P f hP hPD hf hroot hreal E θ V hE hEsub hθ hθ1 hV hmass hval x hx
    have hprod : ENNReal.ofReal θ * MeasureTheory.volume
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 0)) (1 / 2)) ≠ 0 :=
      mul_ne_zero (ENNReal.ofReal_pos.mpr hθ).ne'
        (Metric.measure_closedBall_pos MeasureTheory.volume
          (0 : EuclideanSpace ℝ (Fin 0)) (by norm_num : (0 : ℝ) < 1 / 2)).ne'
    have hEne : MeasureTheory.volume E ≠ 0 := by
      intro he
      apply hprod
      exact le_antisymm (by simpa only [he] using hmass) bot_le
    obtain ⟨y, hy⟩ := MeasureTheory.nonempty_of_measure_ne_zero hEne
    have hbound : ‖f (WithLp.toLp 2 (fun j => (x j : ℂ)))‖ ≤ V := by
      simpa only [Subsingleton.elim x y] using hval y hy
    have hfactor : 1 ≤ θ ^ (-(1 : ℝ)) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hθ hθ1 (by norm_num : -(1 : ℝ) ≤ 0)
    simpa only [one_mul] using hbound.trans (le_mul_of_one_le_left hV hfactor)
  · obtain ⟨C, hC, hbound⟩ :=
      Submission.Obl.k4_algebraic_sheet_remez.exists_sheet_remez_constant n D (Nat.pos_of_ne_zero hn)
    refine ⟨C, hC, ?_⟩
    intro P f hP hPD hf hroot hreal
    exact hbound f ⟨P, hP, hPD, hroot⟩ hf hreal
