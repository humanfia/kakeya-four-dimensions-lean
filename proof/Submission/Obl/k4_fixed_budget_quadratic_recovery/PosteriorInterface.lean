import Submission.Obl.k4_fixed_budget_quadratic_recovery.CoefficientBins

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Set

/-- The finite posterior consequence used by the scalar assembly. Its hypotheses
retain the unnormalized observed component laws and explicit numerical losses. -/
def PosteriorBinRecovery : Prop :=
  ∀ d : ℝ, 0 ≤ d → d < 1 → ∃ e : ℝ, 0 < e ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧
    ∀ R : ℝ, R₀ ≤ R → ∀ n : ℕ,
    ∀ comp : Fin n → Measure (EuclideanSpace ℝ (Fin 3) × ℤ),
    (∀ i, IsFiniteMeasure (comp i)) →
    ∀ (base : (EuclideanSpace ℝ (Fin 3) × ℤ) → ℝ × ℝ)
      (signal : (EuclideanSpace ℝ (Fin 3) × ℤ) → ℝ)
      (F : Fin n → Fin 6 → ℝ) (Y H τ K ρ : ℝ),
    Measurable base → Measurable signal → 1 ≤ Y → 0 < K → 0 ≤ H → 0 < ρ →
    (n : ℝ) ≤ R ^ (d + e) → (∀ i j, |F i j| ≤ H) →
    6 * H * Y ^ 2 ≤ R ^ e → 2 * τ ≤ R ^ (-1 + e) → 864 * R ^ (-e) ≤ ρ →
    (∀ i, ∀ᵐ o ∂comp i, (base o).1 ∈ Icc (0 : ℝ) 1 ∧ |(base o).2| ≤ Y ∧
      |signal o - quadraticValue (F i) (base o).1 (base o).2| ≤ τ) →
    (∀ i E, MeasurableSet E → comp i (base ⁻¹' E) ≤ ENNReal.ofReal K * volume E) →
    ∃ L : (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin 6 → ℤ),
      (∀ q, MeasurableSet {o | q ∈ L o}) ∧ (∀ o, (L o).card ≤ 3 ^ 6) ∧
      (∑ i, comp i).real univ - (n : ℝ) * K * (2 * Y) * R ^ (-2 * e) ≤
        ∑ i, (comp i).real {o | coefficientBin ρ (F i) ∈ L o}

end Submission.Obl.k4_fixed_budget_quadratic_recovery
