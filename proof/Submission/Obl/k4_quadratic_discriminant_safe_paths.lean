import Mathlib
import ChallengeDeps
import Submission.Obl.k4_quadratic_discriminant_safe_paths.AnchorBound
set_option linter.unusedVariables false

/-!
# `Submission.k4_quadratic_discriminant_safe_paths`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_quadratic_discriminant_safe_paths`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_quadratic_discriminant_safe_paths/`
belong to this obligation.
-/

theorem Submission.k4_quadratic_discriminant_safe_paths : ((fun emb : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℂ (Fin 3) => ∃ C : ℕ, 0 < C ∧ ∀ A : ℝ, 2 ≤ A → ∀ P P' : MvPolynomial (Fin 3) ℝ, P.totalDegree ≤ 2 → P'.totalDegree ≤ 2 → (∀ d, |P.coeff d| ≤ A) → (∀ d, |P'.coeff d| ≤ A) → ∀ z₀ : EuclideanSpace ℝ (Fin 3), ‖z₀‖ ≤ (1 : ℝ) / 8 → A⁻¹ ≤ |MvPolynomial.eval (fun i => z₀ i) P| → A⁻¹ ≤ |MvPolynomial.eval (fun i => z₀ i) P'| → (fun bad : Set (EuclideanSpace ℝ (Fin 3) × ℂ) => MeasurableSet bad ∧ (MeasureTheory.volume.prod MeasureTheory.volume) bad ≤ ENNReal.ofReal A⁻¹ * (MeasureTheory.volume.prod MeasureTheory.volume) ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ((1 : ℝ) / 8)) ×ˢ (Metric.closedBall (1 / 2 : ℂ) ((1 : ℝ) / 4)))) {p | p.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ((1 : ℝ) / 8) ∧ p.2 ∈ Metric.closedBall (1 / 2 : ℂ) ((1 : ℝ) / 4) ∧ ∃ z ∈ Metric.thickening (A ^ (-(C : ℝ))) (segment ℝ (emb z₀) (emb z₀ + p.2 • (emb p.1 - emb z₀)) ∪ segment ℝ (emb z₀ + p.2 • (emb p.1 - emb z₀)) (emb p.1)), ‖MvPolynomial.eval (fun i => z i) (P.map (algebraMap ℝ ℂ))‖ < A ^ (-(C : ℝ)) ∨ ‖MvPolynomial.eval (fun i => z i) (P'.map (algebraMap ℝ ℂ))‖ < A ^ (-(C : ℝ))}) (fun z => WithLp.toLp 2 (fun i => (z i : ℂ)))) := by
  obtain ⟨C, hC, h⟩ :=
    Submission.Obl.k4_quadratic_discriminant_safe_paths.safe_paths_from_anchor_bound
      Submission.Obl.k4_quadratic_discriminant_safe_paths.anchorBound
  exact ⟨C, hC, h⟩
