import Submission.Obl.k4_subcritical_chart_projection.Model

set_option linter.unusedVariables false

/-! Shared finite corrected-layer interface, as agreed by x0938 and x0941
in their o264 messages of 2026-10-21T14:57Z and 14:59Z. -/

namespace Submission.Obl.k4_subcritical_chart_projection
open Set MeasureTheory
structure CorrectedLayer (α : Type) where
  n : ℕ
  A : Fin n → Set α
  q : Fin n → Fin 3 → ℤ
  g : Fin n → Fin 6 → ℝ
  P : Fin n → MvPolynomial (Fin 2) ℝ
structure CorrectedLayer.Certified {α : Type} (L : CorrectedLayer α)
    (b : α → Fin 6 → ℝ) (χ D a H B error : ℝ) [MeasurableSpace α] : Prop where
  measurable : ∀ i, MeasurableSet (L.A i)
  disjoint : ∀ i j, i ≠ j → Disjoint (L.A i) (L.A j)
  bins : ∀ i, ∀ l ∈ L.A i, ⌊b l 3 / χ⌋ = L.q i 0 ∧ ⌊b l 0 / D⌋ = L.q i 1 ∧
    ⌊b l 1 / D⌋ = L.q i 2 ∧ (∀ e, |b l e| ≤ H) ∧ |b l 4 + b l 0| ≤ χ
  norm : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1,
    ∀ p ∈ Icc ((L.q i 1 : ℝ) * D) (((L.q i 1 : ℝ) + 1) * D),
    ∀ q ∈ Icc ((L.q i 2 : ℝ) * D) (((L.q i 2 : ℝ) + 1) * D),
      |predictor (L.g i) t p q| ≤ H
  degree : ∀ i, (L.P i).totalDegree ≤ 2
  coeff : ∀ i e, |(L.P i).coeff e| ≤ B
  fit : ∀ i, ∀ l ∈ L.A i, ∀ t ∈ Icc (0 : ℝ) 1,
    |chartSignal a (L.g i) (b l) t -
      MvPolynomial.eval ![t, chartR D (L.q i 1) (L.q i 2) (b l) t] (L.P i)| ≤ error
end Submission.Obl.k4_subcritical_chart_projection
