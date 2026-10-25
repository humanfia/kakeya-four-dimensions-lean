-- Adapted from this LOT tree, obligation o104, session x0472, commit 5cdf90d72f0b.
-- Original file: Submission/Obl/k4_terminal_time_extension/SplitInterfaces.lean
import Submission.Obl.k4_terminal_label_saturation.Interface

namespace Submission.Obl.k4_terminal_label_saturation

noncomputable def trueSys : (ℕ → ℝ) → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop :=
  fun N W ω ν E B f L h => ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ N k ^ ε ∧ ∃ T C' : ℕ, ∃ (γ : Fin C' → Fin (W k)) (j : Fin C' → Fin (2 ^ T)) (c u : Fin C' → EuclideanSpace ℝ (Fin 2)) (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin C' → MvPolynomial (Fin 4) ℝ) (A : Fin C' → Set (ℕ × (Fin 6 → ℝ))) (F : Fin C' → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), N k ^ (h - ε) ≤ (2 : ℝ) ^ T ∧ (2 : ℝ) ^ T ≤ N k ^ (h + ε) ∧ (C' : ℝ) ≤ N k ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧ (∀ b, chart (N k) M D κ T ((j b : ℕ) : ℝ) L (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (ENNReal.ofReal (N k ^ (-f L) * |Matrix.det (Q b)| / ((2 : ℝ) ^ T * κ)) ≤ ((ν k (γ b)).prod MeasureTheory.volume) (F b))) ∧ ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (ω k (γ b)) * ((ν k (γ b)).prod MeasureTheory.volume) (F b)

end Submission.Obl.k4_terminal_label_saturation
