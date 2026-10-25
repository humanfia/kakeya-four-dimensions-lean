/- Adapted within this LOT tree from o120/x0402, commit 81f800489248f55eaf1c2da13f86ceff0ee98719,
Submission/Obl/k4_unbounded_width_exclusion/ReductionInterfaces.lean. -/
import Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarCandidates

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- Continuous base caps supplement the scalar mesh bounds. These are what
control the index/base marginals in posterior matching. -/
def ProjectedScalarLaw
    (N η d s m S U : ℝ) (ν : MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (μ : MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (b : (ℕ × (Fin 6 → ℝ)) → Fin 5 → ℝ) : Prop :=
  ScalarAdmissible N η d s m 1 S U 1 ν b μ ∧
  ∀ (r : ℝ) (j : ℤ) (E : Set (EuclideanSpace ℝ (Fin 2))),
    0 ≤ r → r ≤ s → MeasurableSet E →
    μ {p | WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] ∈ E ∧
      ⌊scalarX (b p.1) p.2 / (N ^ (-r))⌋ = j} ≤
      ENNReal.ofReal (N ^ η * (N ^ (-r)) ^ d) * MeasureTheory.volume E

/-- A finite recovery statement, with an arbitrary specified original observation.
Output assignments are geometric sets in the five scalar coefficients. -/
def FixedBudgetQuadraticRecovery : Prop :=
  ∀ d s m S U : ℝ, 0 ≤ d → d < 1 → 0 < s → s < 1 → s < m → 0 < S → 0 < U → U < m →
  ∃ c : ℝ, 0 < c ∧ c < min s 1 ∧ ∃ M D : ℕ, 1 ≤ M ∧
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
  ∀ N : ℝ, N₀ ≤ N →
  ∀ (ν : MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (μ : MeasureTheory.Measure ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (b : (ℕ × (Fin 6 → ℝ)) → Fin 5 → ℝ)
    (O : ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 3) × ℤ)
    (base : (EuclideanSpace ℝ (Fin 3) × ℤ) → EuclideanSpace ℝ (Fin 2))
    (signal : (EuclideanSpace ℝ (Fin 3) × ℤ) → ℝ),
    ProjectedScalarLaw N η d s m S U ν μ b →
    ENNReal.ofReal (N ^ (-η)) ≤ μ Set.univ →
    Measurable O → Measurable base → Measurable signal →
    (∀ᵐ p ∂μ, base (O p) = WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] ∧
      |scalarX (b p.1) p.2 - signal (O p)| ≤ N ^ (-1 + η)) →
    ∃ (n : ℕ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
      (A : Fin n → Set (Fin 5 → ℝ))
      (lst : (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin n)),
      (n : ℝ) ≤ N ^ (d * s + ε) ∧
      (∀ i, (P i).totalDegree ≤ 2 ∧ (∀ e, |(P i).coeff e| ≤ N ^ ε) ∧
        MeasurableSet (A i) ∧ fmt 5 (N ^ M) D (A i) ∧
        ∀ z ∈ A i, ∀ t ∈ Set.Icc (0 : ℝ) 1,
          |scalarX z t - MvPolynomial.eval ![t, scalarY z t] (P i)| ≤ N ^ (-c)) ∧
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
      (∀ o, (lst o).card ≤ M) ∧
      (∀ i, MeasurableSet {o | i ∈ lst o}) ∧
      ENNReal.ofReal (1 / 2 : ℝ) * μ Set.univ ≤
        μ {p | ∃ i, b p.1 ∈ A i ∧ i ∈ lst (O p)}

end Submission.Obl.k4_fixed_budget_quadratic_recovery
