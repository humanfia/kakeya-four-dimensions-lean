import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Interface

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing

open MeasureTheory

/-- Readable form of the frozen statement. -/
def SmoothingStatement : Prop :=
  ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop →
    Subpower N K → ∀ d s m C S U : ℝ,
    0 ≤ d → d < 1 → 0 < s → s < m → 0 < C → 0 < S → 0 < U → U < m →
    ∀ (α : ℕ → Type) [∀ k, MeasurableSpace (α k)]
      (ν : (k : ℕ) → Measure (α k)) (μ : (k : ℕ) → Measure (α k × ℝ))
      (b : (k : ℕ) → α k → Coeff) (c : ℕ → ℝ) (angular : ℕ → Bool),
      (∀ k, N k ^ (-C) ≤ c k ∧ c k ≤ N k ^ C) →
      (∀ k, MeshInput (N k) (K k) d s m S U (α k) (ν k) (μ k) (b k) (c k) (angular k)) →
      ∃ K' : ℕ → ℝ, Subpower N K' ∧
      ∃ (M : ℕ) (H J : ℕ → ℕ) (b₀ : (k : ℕ) → Fin (H k) → Coeff)
        (w : (k : ℕ) → Fin (H k) → ℝ)
        (mark : (k : ℕ) → Fin (H k) → Fin (J k) → Bool)
        (tag : (k : ℕ) → α k → Fin (H k)),
        (∀ k, Tables (N k) (K' k) m M (H k) (J k) (b₀ k) (w k) (mark k)) ∧
        (∀ k, Coupling (N k) (K' k) s m (α k) (ν k) (μ k) (b k) (H k) (J k)
          (tag k) (b₀ k) (w k) (mark k)) ∧
        (∀ k, RawEstimates (N k) (K' k) d s m S U (c k) (angular k)
          (MarkedLaw (N k ^ (-m)) (H k) (J k) (b₀ k) (w k) (mark k)))

/-- A fixed-model analytic bound, separated from finite construction and sequence bookkeeping. -/
def LocalRawSmoothingBound (A : ℝ) (p : ℕ) : Prop :=
  ∀ (N K d s m S U c : ℝ) (angular : Bool),
    2 ≤ N → 1 ≤ K → 0 ≤ d → d < 1 → 0 < s → s < m →
    0 < S → 0 < U → U < m → 0 < c →
    ∀ (α : Type) [MeasurableSpace α] (ν : Measure α) (μ : Measure (α × ℝ)) (b : α → Coeff),
      MeshInput N K d s m S U α ν μ b c angular →
      ∀ (H J : ℕ) (tag : α → Fin H) (b₀ : Fin H → Coeff) (w : Fin H → ℝ)
        (mark : Fin H → Fin J → Bool),
      1 ≤ J → 1 ≤ (J : ℝ) * N ^ (-m) → (J : ℝ) * N ^ (-m) ≤ 2 →
      (∀ j, 0 ≤ w j) → (∑ j, w j) = 1 →
      (∀ j i, |b₀ j i| ≤ K + N ^ (-10 * (m + s + 1))) →
      Measurable tag → (∀ j, ENNReal.ofReal (w j) = ν {l | tag l = j}) →
      (∀ l e, |b l e - b₀ (tag l) e| ≤ N ^ (-10 * (m + s + 1))) →
      (∀ j z, mark j z = true →
        ENNReal.ofReal (w j / ((J : ℝ) * (2 * K))) ≤
          μ {q | tag q.1 = j ∧ q.2 ∈ timeCell J z}) →
      RawEstimates N (A * K ^ p) d s m S U c angular
        (MarkedLaw (N ^ (-m)) H J b₀ w mark)

end Submission.Obl.k4_scalar_marked_coefficient_smoothing
