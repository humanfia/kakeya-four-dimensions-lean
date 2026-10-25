/- Adapted from same-tree o119, session x0401, commit 19d6f4b3eda81f6d7228948a9996d889733ab672,
   Submission/Obl/k4_finite_width_critical_contradiction/Expanded.lean (namespace renamed; any
   earlier provenance is kept below). -/
import Submission.Obl.k4_finite_width_path_realization.Toolkit.InitialBridge
import Submission.Obl.k4_finite_width_path_realization.Toolkit.ExtremalSetup

/-! Directly named immediately applied lambdas from the frozen o119 type. -/
namespace Submission.Obl.k4_finite_width_path_realization
set_option linter.unusedVariables false

noncomputable def ExpandedTerminal : (ℕ → ℝ) → (ℕ → ℝ) → ℝ → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → ℝ) → (ℝ → ℝ) → ℝ → Prop :=
  (fun N K L W ω ν E B f h => ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ κ : ℝ, 1 ≤ κ ∧ K k ≤ κ ∧ κ ≤ N k ^ ε ∧ ∃ T C' : ℕ, ∃ (γ : Fin (C') → Fin (W k)) (j : Fin (C') → Fin (2 ^ T)) (c u : Fin (C') → EuclideanSpace ℝ (Fin 2)) (Q : Fin (C') → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin (C') → MvPolynomial (Fin 4) ℝ) (A : Fin (C') → Set (ℕ × (Fin 6 → ℝ))) (F : Fin (C') → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), (2 : ℝ) ^ T ≤ N k ^ h ∧ (C' : ℝ) ≤ N k ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧ (∀ b, Chart (N k) M D κ T ((j b : ℕ) : ℝ) L (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (ENNReal.ofReal (N k ^ (-f L) * |Matrix.det (Q b)| / ((2 : ℝ) ^ T * κ)) ≤ (((ν k (γ b)).prod MeasureTheory.volume) (F b)))) ∧ ENNReal.ofReal ((κ)⁻¹) ≤ ∑ b, ENNReal.ofReal (ω k (γ b)) * (((ν k (γ b)).prod MeasureTheory.volume) (F b)))

noncomputable def ExpandedNarrowTerminal : (ℕ → ℝ) → (ℕ → ℝ) → ℝ → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop :=
  (fun N K L W ω ν E B f h w => ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ κ : ℝ, 1 ≤ κ ∧ K k ≤ κ ∧ κ ≤ N k ^ ε ∧ ∃ T C' : ℕ, ∃ (γ : Fin (C') → Fin (W k)) (j : Fin (C') → Fin (2 ^ T)) (c u : Fin (C') → EuclideanSpace ℝ (Fin 2)) (Q : Fin (C') → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin (C') → MvPolynomial (Fin 4) ℝ) (A : Fin (C') → Set (ℕ × (Fin 6 → ℝ))) (F : Fin (C') → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), (2 : ℝ) ^ T ≤ N k ^ (h + ε) ∧ (∀ b, |Matrix.det (Q b)| * (4 : ℝ) ^ T ≤ N k ^ (-w + ε)) ∧ (C' : ℝ) ≤ N k ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧ (∀ b, Chart (N k) M D κ T ((j b : ℕ) : ℝ) L (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (ENNReal.ofReal (N k ^ (-f L) * |Matrix.det (Q b)| / ((2 : ℝ) ^ T * κ)) ≤ (((ν k (γ b)).prod MeasureTheory.volume) (F b)))) ∧ ENNReal.ofReal ((κ)⁻¹) ≤ ∑ b, ENNReal.ofReal (ω k (γ b)) * (((ν k (γ b)).prod MeasureTheory.volume) (F b)))

noncomputable def ExpandedHorizon : (ℕ → ℝ) → (ℕ → ℝ) → ℝ → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → ℝ) → (ℝ → ℝ) → ℝ :=
  (fun N K L W ω ν E B f => sInf {h : ℝ | ExpandedTerminal N K L W ω ν E B f h})

noncomputable def ExpandedExtremalSetup : ℝ → ℝ → ℝ → ℝ → Prop :=
  (fun ds kr S η => 0 ≤ ds ∧ ds < 1 ∧ 0 < kr ∧ kr ≤ 1 ∧ (∀ t : ℝ, 0 < t → ∃ N K d W ω ν E P B f g G, Problem N K 1 d S η W ω ν E P B f g G ∧ d < ds + t ∧ kr - t < ExpandedHorizon N K 1 W ω ν E B f) ∧ (∀ t : ℝ, 0 < t → ∃ a : ℝ, 0 < a ∧ ∀ N K L d W ω ν E P B f g G, Problem N K L d S η W ω ν E P B f g G → d < ds + a → ExpandedHorizon N K L W ω ν E B f ≤ (kr + t) * L) ∧ (∀ t : ℝ, 0 < t → ∃ a : ℝ, 0 < a ∧ ∀ N K L d W ω ν E P B f g G, Problem N K L d S η W ω ν E P B f g G → d < ds + a → (kr - a) * L < ExpandedHorizon N K L W ω ν E B f → ∀ r : ℝ, 0 ≤ r → r ≤ L → |f r - f 0 - ds * r| ≤ t * L))

noncomputable def ExpandedBoundedWidth : ℝ → ℝ → ℝ → ℝ → Prop :=
  (fun ds kr S η => ∃ a w : ℝ, 0 < a ∧ 0 ≤ w ∧ ∀ t : ℝ, 0 < t → ∃ N K d W ω ν E P B f g G, Problem N K 1 d S η W ω ν E P B f g G ∧ d < ds + t ∧ kr - t < ExpandedHorizon N K 1 W ω ν E B f ∧ ¬ ExpandedNarrowTerminal N K 1 W ω ν E B f (kr + a) w)

end Submission.Obl.k4_finite_width_path_realization
