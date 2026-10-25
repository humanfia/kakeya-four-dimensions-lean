import Submission.Obl.k4_matching_homogeneous_records.Input

namespace Submission.Obl.k4_matching_homogeneous_records

def SelectionStatement : Prop :=
  ∀ (q : ℕ) (s : ℝ), 0 ≤ s → ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ R : ℝ, 2 ≤ R ∧ ∀ N : ℝ, R ≤ N → ∀ (α : Type) [MeasurableSpace α] (μ : MeasureTheory.Measure α) (F : ℕ → α → ℕ) (S : Set α), MeasureTheory.IsProbabilityMeasure μ → MeasurableSet S → μ Sᶜ = 0 → (∀ k : ℕ, k ≤ q → Measurable (F k) ∧ (F k '' S).Finite) → (∀ a b : ℕ, a ≤ b → b ≤ q → ∀ x ∈ S, ∀ y ∈ S, F b x = F b y → F a x = F a y) → ((F q '' S).ncard : ℝ) ≤ N ^ (s + η) → ∃ (u : ℕ → ℝ) (ν : MeasureTheory.Measure α) (T : Set α), ((∀ k : ℕ, k ≤ q → 0 ≤ u k) ∧ (∀ a b : ℕ, a ≤ b → b ≤ q → u a ≤ u b) ∧ u q ≤ s + ε) ∧ MeasureTheory.IsProbabilityMeasure ν ∧ (∀ E : Set α, ν E ≤ ENNReal.ofReal (N ^ ε) * μ E) ∧ T ⊆ S ∧ MeasurableSet T ∧ ν Tᶜ = 0 ∧ (∀ k : ℕ, k ≤ q → ((F k '' T).ncard : ℝ) ≤ N ^ (u k + ε)) ∧ (∀ a b : ℕ, a ≤ b → b ≤ q → ∀ x ∈ T, ((F b '' {y | y ∈ T ∧ F a y = F a x}).ncard : ℝ) ≤ N ^ (u b - u a + ε))

def CompactnessStatement : Prop :=
  ∀ (q : ℕ) (s : ℝ), 0 ≤ s → ∀ P : (ℕ → ℝ) → ℝ → ℝ → Prop, (∀ (u v : ℕ → ℝ) (ε δ N : ℝ), 0 < ε → 0 < δ → 2 ≤ N → (∀ k : ℕ, k ≤ q → |u k - v k| ≤ δ) → P u ε N → P v (ε + 2 * δ) N) → (∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 2 ≤ R → ∃ N : ℝ, R ≤ N ∧ ∃ u : ℕ → ℝ, ((∀ k : ℕ, k ≤ q → 0 ≤ u k) ∧ (∀ a b : ℕ, a ≤ b → b ≤ q → u a ≤ u b) ∧ u q ≤ s + ε) ∧ P u ε N) → ∃ u : ℕ → ℝ, ((∀ k : ℕ, k ≤ q → 0 ≤ u k) ∧ (∀ a b : ℕ, a ≤ b → b ≤ q → u a ≤ u b) ∧ u q ≤ s) ∧ (∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 2 ≤ R → ∃ N : ℝ, R ≤ N ∧ P u ε N)

end Submission.Obl.k4_matching_homogeneous_records
