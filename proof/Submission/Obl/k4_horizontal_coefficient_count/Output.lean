import Submission.Obl.k4_horizontal_coefficient_count.Families

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- The frozen full-time conclusion at one sample, without its mass floor. -/
def Layers {α : Type*} [MeasurableSpace α]
    (N d e₀ u ε R : ℝ) {m : ℕ} (sH : Fin m → ℝ)
    (ρ : Measure (α × ℝ)) (π : Measure ℝ) (b : α → Fin 6 → ℝ) : Prop :=
  ∃ (nH : Fin m → ℕ) (AH : (r : Fin m) → Fin (nH r) → Set α)
    (qH : (r : Fin m) → Fin (nH r) → Fin 3 → ℤ)
    (hH : (r : Fin m) → Fin (nH r) → Fin 6 → ℝ),
    ∀ r, (fun (χ D a : ℝ) =>
      (∀ i, MeasurableSet (AH r i)) ∧
      (∀ i i', i ≠ i' → Disjoint (AH r i) (AH r i')) ∧
      (∀ i,
        (∀ l ∈ AH r i, ⌊b l 3 / χ⌋ = qH r i 0 ∧
          ⌊b l 0 / D⌋ = qH r i 1 ∧ ⌊b l 1 / D⌋ = qH r i 2) ∧
        (∀ e, |hH r i e| ≤ N ^ R) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          ∀ p ∈ Icc ((qH r i 1 : ℝ) * D) (((qH r i 1 : ℝ) + 1) * D),
          ∀ q ∈ Icc ((qH r i 2 : ℝ) * D) (((qH r i 2 : ℝ) + 1) * D),
            |predictor (hH r i) t p q| ≤ N ^ ε) ∧
        (∀ l ∈ AH r i, ∀ t ∈ Icc (0 : ℝ) 1,
          |b l 2 + t * b l 5 - predictor (hH r i) t (b l 0) (b l 1)| ≤ N ^ ε * a) ∧
        ENNReal.ofReal (D ^ 2 * a ^ d / N ^ ε) *
            π (Ico ((qH r i 0 : ℝ) * χ) (((qH r i 0 : ℝ) + 1) * χ)) ≤
          ρ (AH r i ×ˢ Icc (0 : ℝ) 1)) ∧
      ρ {p | ∃ i, p.1 ∈ AH r i}ᶜ = 0)
      (N ^ (-e₀)) (N ^ (-u * sH r)) (N ^ (-sH r))

theorem layers_of_families {α : Type*} [MeasurableSpace α]
    (N d e₀ u ε R : ℝ) {m : ℕ} (sH : Fin m → ℝ)
    (ρ : Measure (α × ℝ)) (π : Measure ℝ) (b : α → Fin 6 → ℝ)
    (f : (r : Fin m) → PredictorFamily b (N ^ (-e₀)) (N ^ (-u * sH r))
      (N ^ (-sH r)) (N ^ R) (N ^ ε))
    (hc : ∀ r, (f r).Covers ρ)
    (hf : ∀ r, (f r).Floors π d (N ^ ε) ρ) :
    Layers N d e₀ u ε R sH ρ π b := by
  refine ⟨fun r => (f r).n, fun r => (f r).A, fun r => (f r).q,
    fun r => (f r).h, ?_⟩
  intro r
  exact ⟨(f r).measurable, (f r).disjoint,
    fun i => ⟨(f r).bins i, (f r).coefficients i, (f r).norm i, (f r).fit i, hf r i⟩,
    hc r⟩

end Submission.Obl.k4_horizontal_coefficient_count
