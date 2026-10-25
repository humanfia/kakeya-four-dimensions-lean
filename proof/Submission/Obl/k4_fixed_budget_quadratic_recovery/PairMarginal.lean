import Submission.Obl.k4_fixed_budget_quadratic_recovery.MarginalCaps

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Set

/-- The scalar base can be written as a real pair without changing Lebesgue volume. -/
theorem volume_euclidean_pair_preimage (E : Set (ℝ × ℝ)) (hE : MeasurableSet E) :
    volume {q : EuclideanSpace ℝ (Fin 2) | (q 0, q 1) ∈ E} = volume E := by
  have hp := (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  exact hp.measure_preimage hE.nullMeasurableSet

/-- Continuous scalar-bin caps give the same label marginal in real-pair coordinates. -/
theorem scalarFit_pair_marginal_cap_power
    {N η d s m S U δ : ℝ} (hN : 1 ≤ N) (hs : 0 ≤ s) (hδ : 0 ≤ δ)
    {ν : Measure (ℕ × (Fin 6 → ℝ))}
    {μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {b : (ℕ × (Fin 6 → ℝ)) → Fin 5 → ℝ}
    (hlaw : ProjectedScalarLaw N η d s m S U ν μ b)
    (P : MvPolynomial (Fin 2) ℝ) (A : Set (Fin 5 → ℝ))
    (hA : A ⊆ scalarFit P (N ^ δ * N ^ (-s)))
    (E : Set (ℝ × ℝ)) (hE : MeasurableSet E) :
    μ {p | b p.1 ∈ A ∧ (p.2, scalarY (b p.1) p.2) ∈ E} ≤
      ENNReal.ofReal (7 * N ^ (η + δ - d * s)) * volume E := by
  let E' : Set (EuclideanSpace ℝ (Fin 2)) := {q | (q 0, q 1) ∈ E}
  have hE' : MeasurableSet E' := hE.preimage (by fun_prop)
  have h := scalarFit_marginal_cap_power hN hs hδ hlaw P A hA E' hE'
  have hvol : volume E' = volume E := volume_euclidean_pair_preimage E hE
  rw [hvol] at h
  exact h

end Submission.Obl.k4_fixed_budget_quadratic_recovery
