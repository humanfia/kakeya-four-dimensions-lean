import Submission.Obl.k4_scalar_marked_profile_selection.Interface

noncomputable section

namespace Submission.Obl.k4_scalar_marked_profile_selection

open MeasureTheory Set Filter

abbrev selectionStatement : Prop :=
  ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Tendsto N atTop atTop → Subpower N K →
  ∀ d s m C S U : ℝ, 0 ≤ d → d < 1 → 0 < s → s < m → 0 < C →
    0 < S → 0 < U → U < m →
  ∀ (c : ℕ → ℝ) (angular : ℕ → Bool) (M : ℕ) (H J : ℕ → ℕ)
    (b : (k : ℕ) → Fin (H k) → Fin 5 → ℝ) (w : (k : ℕ) → Fin (H k) → ℝ)
    (mark : (k : ℕ) → Fin (H k) → Fin (J k) → Bool),
    (∀ k, N k ^ (-C) ≤ c k ∧ c k ≤ N k ^ C) →
    (∀ k, tables (N k) (K k) m M (H k) (J k) (b k) (w k) (mark k)) →
    (∀ k, raw (N k) (K k) d s m S U (c k) (angular k)
      (law (N k ^ (-m)) (H k) (J k) (b k) (w k) (mark k))) →
  ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ K' : ℕ → ℝ,
    Subpower (N ∘ ψ) K' ∧ (∀ k, K (ψ k) ≤ K' k) ∧
  ∃ (mark' : (k : ℕ) → Fin (H (ψ k)) → Fin (J (ψ k)) → Bool) (angular₀ : Bool),
    (∀ k, angular (ψ k) = angular₀) ∧ ∃ (C₀ : ℝ) (F : ℝ → ℝ → ℝ),
    profileShape d s m S U C₀ angular₀ F ∧
    (∀ τ : ℝ, 0 < τ → ∀ᶠ k in atTop,
      N (ψ k) ^ (C₀ - τ) ≤ c (ψ k) ∧ c (ψ k) ≤ N (ψ k) ^ (C₀ + τ)) ∧
    (∀ k, tables (N (ψ k)) (K' k) m M (H (ψ k)) (J (ψ k))
      (b (ψ k)) (w (ψ k)) (mark' k)) ∧
    (∀ k j z, mark' k j z = true → mark (ψ k) j z = true) ∧
    homogeneous (N ∘ ψ) s (4 * (m + s + 1))
      (fun k => law (N (ψ k) ^ (-m)) (H (ψ k)) (J (ψ k))
        (b (ψ k)) (w (ψ k)) (mark' k)) F

abbrev gridSelectionStatement : Prop :=
  ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Tendsto N atTop atTop → Subpower N K →
  ∀ s m V : ℝ, 0 < s → s < m → 0 < V →
  ∀ (M : ℕ) (H J : ℕ → ℕ) (b : (k : ℕ) → Fin (H k) → Fin 5 → ℝ)
    (w : (k : ℕ) → Fin (H k) → ℝ)
    (mark : (k : ℕ) → Fin (H k) → Fin (J k) → Bool),
  (∀ k, tables (N k) (K k) m M (H k) (J k) (b k) (w k) (mark k)) →
  ∃ L : ℕ → ℝ, Subpower N L ∧ (∀ k, K k ≤ L k) ∧
  ∃ mark' : (k : ℕ) → Fin (H k) → Fin (J k) → Bool,
    (∀ k, tables (N k) (L k) m M (H k) (J k) (b k) (w k) (mark' k)) ∧
    (∀ k j z, mark' k j z = true → mark k j z = true) ∧
    gridData N s V (fun k => law (N k ^ (-m)) (H k) (J k) (b k) (w k) (mark' k))

abbrev gridExtensionStatement : Prop :=
  ∀ (N K : ℕ → ℝ) (μ : ℕ → Measure Incidence),
  (∀ k, 2 ≤ N k) → Tendsto N atTop atTop → Subpower N K →
  ∀ s V : ℝ, 0 < s → 0 < V →
  (∀ k, ENNReal.ofReal ((K k)⁻¹) ≤ μ k univ ∧ μ k univ ≤ 1) →
  gridData N s V μ →
  ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ F : ℝ → ℝ → ℝ,
    regular s V F ∧ homogeneous (N ∘ ψ) s V (μ ∘ ψ) F

abbrev rawCertificationStatement : Prop :=
  ∀ (N K L : ℕ → ℝ), (∀ k, 2 ≤ N k) → Tendsto N atTop atTop →
  Subpower N K → Subpower N L →
  ∀ d s m C S U : ℝ, 0 ≤ d → d < 1 → 0 < s → s < m → 0 < C →
    0 < S → 0 < U → U < m →
  ∀ (c : ℕ → ℝ) (angular : ℕ → Bool) (μ ν : ℕ → Measure Incidence),
    (∀ k, N k ^ (-C) ≤ c k ∧ c k ≤ N k ^ C) →
    (∀ k, ν k ≤ μ k) → (∀ k, ENNReal.ofReal ((L k)⁻¹) ≤ ν k univ) →
    (∀ k, raw (N k) (K k) d s m S U (c k) (angular k) (μ k)) →
  ∀ F : ℝ → ℝ → ℝ, homogeneous N s (4 * (m + s + 1)) ν F →
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (angular₀ : Bool) (C₀ : ℝ),
    (∀ k, angular (φ k) = angular₀) ∧
    (∀ τ : ℝ, 0 < τ → ∀ᶠ k in atTop,
      N (φ k) ^ (C₀ - τ) ≤ c (φ k) ∧ c (φ k) ≤ N (φ k) ^ (C₀ + τ)) ∧
    numerical d s m S U C₀ angular₀ F

end Submission.Obl.k4_scalar_marked_profile_selection
