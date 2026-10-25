import Submission.Obl.k4_scalar_mesh_block_reduction.Interfaces

namespace Submission.Obl.k4_scalar_mesh_block_reduction

def marked_smoothing_type : Prop :=
  ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → Subpower N K →
  ∀ d s m C S U : ℝ, 0 ≤ d → d < 1 → 0 < s → s < m → 0 < C → 0 < S → 0 < U → U < m →
  ∀ (α : ℕ → Type) [∀ k, MeasurableSpace (α k)]
  (ν : (k : ℕ) → MeasureTheory.Measure (α k)) (μ : (k : ℕ) → MeasureTheory.Measure (α k × ℝ))
  (b : (k : ℕ) → α k → Fin 5 → ℝ) (c : ℕ → ℝ) (angular : ℕ → Bool),
  (∀ k, N k ^ (-C) ≤ c k ∧ c k ≤ N k ^ C) →
  (∀ k, MeshInput (N k) (K k) d s m S U (α k) (ν k) (μ k) (b k) (c k) (angular k)) →
  ∃ K' : ℕ → ℝ, Subpower N K' ∧ ∃ (M : ℕ) (H J : ℕ → ℕ) (b₀ : (k : ℕ) → Fin (H k) → Fin 5 → ℝ)
  (w : (k : ℕ) → Fin (H k) → ℝ) (mark : (k : ℕ) → Fin (H k) → Fin (J k) → Bool)
  (tag : (k : ℕ) → α k → Fin (H k)),
  (∀ k, Tables (N k) (K' k) m M (H k) (J k) (b₀ k) (w k) (mark k)) ∧
  (∀ k, Coupling (N k) (K' k) s m (α k) (ν k) (μ k) (b k) (H k) (J k) (tag k) (b₀ k) (w k) (mark k)) ∧
  (∀ k, RawEstimates (N k) (K' k) d s m S U (c k) (angular k) (MarkedLaw (N k ^ (-m)) (H k) (J k) (b₀ k) (w k) (mark k)))

def profile_selection_type : Prop :=
  ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → Subpower N K →
  ∀ d s m C S U : ℝ, 0 ≤ d → d < 1 → 0 < s → s < m → 0 < C → 0 < S → 0 < U → U < m →
  ∀ (c : ℕ → ℝ) (angular : ℕ → Bool) (M : ℕ) (H J : ℕ → ℕ) (b₀ : (k : ℕ) → Fin (H k) → Fin 5 → ℝ)
  (w : (k : ℕ) → Fin (H k) → ℝ) (mark : (k : ℕ) → Fin (H k) → Fin (J k) → Bool),
  (∀ k, N k ^ (-C) ≤ c k ∧ c k ≤ N k ^ C) →
  (∀ k, Tables (N k) (K k) m M (H k) (J k) (b₀ k) (w k) (mark k)) →
  (∀ k, RawEstimates (N k) (K k) d s m S U (c k) (angular k) (MarkedLaw (N k ^ (-m)) (H k) (J k) (b₀ k) (w k) (mark k))) →
  ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ K' : ℕ → ℝ, Subpower (N ∘ ψ) K' ∧ (∀ k, K (ψ k) ≤ K' k) ∧
  ∃ (mark' : (k : ℕ) → Fin (H (ψ k)) → Fin (J (ψ k)) → Bool) (angular₀ : Bool),
  (∀ k, angular (ψ k) = angular₀) ∧ ∃ (C₀ : ℝ) (F : ℝ → ℝ → ℝ),
  ProfileShape d s m S U C₀ angular₀ F ∧
  (∀ τ : ℝ, 0 < τ → ∀ᶠ k in Filter.atTop, N (ψ k) ^ (C₀ - τ) ≤ c (ψ k) ∧ c (ψ k) ≤ N (ψ k) ^ (C₀ + τ)) ∧
  (∀ k, Tables (N (ψ k)) (K' k) m M (H (ψ k)) (J (ψ k)) (b₀ (ψ k)) (w (ψ k)) (mark' k)) ∧
  (∀ k j z, mark' k j z = true → mark (ψ k) j z = true) ∧
  Homogeneous (N ∘ ψ) s (4 * (m + s + 1))
  (fun k => MarkedLaw (N (ψ k) ^ (-m)) (H (ψ k)) (J (ψ k)) (b₀ (ψ k)) (w (ψ k)) (mark' k)) F

def noisy_packets_type : Prop :=
  ExactAngularPackets →
  ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → Subpower N K →
  ∀ d s m C S U : ℝ, 0 ≤ d → d < 1 → 0 < s → s < m → 0 < C → 0 < S → 0 < U → U < m →
  ∀ (c : ℕ → ℝ) (angular : Bool) (C₀ : ℝ) (F : ℝ → ℝ → ℝ) (M : ℕ) (H J : ℕ → ℕ) (b₀ : (k : ℕ) → Fin (H k) → Fin 5 → ℝ)
  (w : (k : ℕ) → Fin (H k) → ℝ) (mark : (k : ℕ) → Fin (H k) → Fin (J k) → Bool),
  (∀ k, N k ^ (-C) ≤ c k ∧ c k ≤ N k ^ C) →
  (∀ k, Tables (N k) (K k) m M (H k) (J k) (b₀ k) (w k) (mark k)) →
  ProfileShape d s m S U C₀ angular F →
  (∀ τ : ℝ, 0 < τ → ∀ᶠ k in Filter.atTop, N k ^ (C₀ - τ) ≤ c k ∧ c k ≤ N k ^ (C₀ + τ)) →
  Homogeneous N s (4 * (m + s + 1))
  (fun k => MarkedLaw (N k ^ (-m)) (H k) (J k) (b₀ k) (w k) (mark k)) F →
  ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop,
  NoisyOutput (N k) d s m (c k) ε angular (MarkedLaw (N k ^ (-m)) (H k) (J k) (b₀ k) (w k) (mark k))

def original_recovery_type : Prop :=
  ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → Subpower N K →
  ∀ d s m : ℝ, 0 ≤ d → d < 1 → 0 < s → s < m →
  ∀ (α : ℕ → Type) [∀ k, MeasurableSpace (α k)]
  (ν : (k : ℕ) → MeasureTheory.Measure (α k)) (μ : (k : ℕ) → MeasureTheory.Measure (α k × ℝ))
  (b : (k : ℕ) → α k → Fin 5 → ℝ) (c : ℕ → ℝ) (angular : ℕ → Bool),
  ∀ (M : ℕ) (H J : ℕ → ℕ) (b₀ : (k : ℕ) → Fin (H k) → Fin 5 → ℝ)
  (w : (k : ℕ) → Fin (H k) → ℝ) (mark : (k : ℕ) → Fin (H k) → Fin (J k) → Bool) (tag : (k : ℕ) → α k → Fin (H k)),
  (∀ k, Tables (N k) (K k) m M (H k) (J k) (b₀ k) (w k) (mark k)) →
  (∀ k, Coupling (N k) (K k) s m (α k) (ν k) (μ k) (b k) (H k) (J k) (tag k) (b₀ k) (w k) (mark k)) →
  (∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop,
  NoisyOutput (N k) d s m (c k) ε (angular k) (MarkedLaw (N k ^ (-m)) (H k) (J k) (b₀ k) (w k) (mark k))) →
  ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop,
  BlockOutput (N k) d s m (c k) ε (angular k) (α k) (μ k) (b k)

end Submission.Obl.k4_scalar_mesh_block_reduction
