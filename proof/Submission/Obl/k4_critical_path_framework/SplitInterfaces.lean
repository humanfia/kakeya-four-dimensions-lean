import Submission.Obl.k4_critical_path_framework.Bridge

/-! Mathlib-only predicates used in the three-child cut.
The frozen statements expand these definitions with immediately applied lambdas.
-/
namespace Submission.Obl.k4_critical_path_framework

set_option linter.unusedVariables false

noncomputable def TerminalExpanded : (ℕ → ℝ) → (ℕ → ℝ) → ℝ → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → ℝ) → (ℝ → ℝ) → ℝ → Prop :=
  fun N K L W ω ν E B f h => ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ κ : ℝ, 1 ≤ κ ∧ K k ≤ κ ∧ κ ≤ N k ^ ε ∧ ∃ T C' : ℕ, ∃ (γ : Fin (C') → Fin (W k)) (j : Fin (C') → Fin (2 ^ T)) (c u : Fin (C') → EuclideanSpace ℝ (Fin 2)) (Q : Fin (C') → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin (C') → MvPolynomial (Fin 4) ℝ) (A : Fin (C') → Set (ℕ × (Fin 6 → ℝ))) (F : Fin (C') → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), (2 : ℝ) ^ T ≤ N k ^ h ∧ (C' : ℝ) ≤ N k ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧ (∀ b, Chart (N k) M D κ T ((j b : ℕ) : ℝ) L (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (ENNReal.ofReal (N k ^ (-f L) * |Matrix.det (Q b)| / ((2 : ℝ) ^ T * κ)) ≤ (((ν k (γ b)).prod MeasureTheory.volume) (F b)))) ∧ ENNReal.ofReal ((κ)⁻¹) ≤ ∑ b, ENNReal.ofReal (ω k (γ b)) * (((ν k (γ b)).prod MeasureTheory.volume) (F b))

noncomputable def HorizonExpanded : (ℕ → ℝ) → (ℕ → ℝ) → ℝ → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → ℝ) → (ℝ → ℝ) → ℝ :=
  fun N K L W ω ν E B f => sInf {h : ℝ | TerminalExpanded N K L W ω ν E B f h}

noncomputable def NarrowTerminalExpanded : (ℕ → ℝ) → (ℕ → ℝ) → ℝ → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop :=
  fun N K L W ω ν E B f h w => ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ κ : ℝ, 1 ≤ κ ∧ K k ≤ κ ∧ κ ≤ N k ^ ε ∧ ∃ T C' : ℕ, ∃ (γ : Fin (C') → Fin (W k)) (j : Fin (C') → Fin (2 ^ T)) (c u : Fin (C') → EuclideanSpace ℝ (Fin 2)) (Q : Fin (C') → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin (C') → MvPolynomial (Fin 4) ℝ) (A : Fin (C') → Set (ℕ × (Fin 6 → ℝ))) (F : Fin (C') → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), (2 : ℝ) ^ T ≤ N k ^ (h + ε) ∧ (∀ b, |Matrix.det (Q b)| * (4 : ℝ) ^ T ≤ N k ^ (-w + ε)) ∧ (C' : ℝ) ≤ N k ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧ (∀ b, Chart (N k) M D κ T ((j b : ℕ) : ℝ) L (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (ENNReal.ofReal (N k ^ (-f L) * |Matrix.det (Q b)| / ((2 : ℝ) ^ T * κ)) ≤ (((ν k (γ b)).prod MeasureTheory.volume) (F b)))) ∧ ENNReal.ofReal ((κ)⁻¹) ≤ ∑ b, ENNReal.ofReal (ω k (γ b)) * (((ν k (γ b)).prod MeasureTheory.volume) (F b))

noncomputable def ExtremalSetup : ℝ → ℝ → ℝ → ℝ → Prop :=
  fun ds kr S η =>
  0 ≤ ds ∧ ds < 1 ∧ 0 < kr ∧ kr ≤ 1 ∧
  (∀ t : ℝ, 0 < t → ∃ N K d W ω ν E P B f g G,
    Problem N K 1 d S η W ω ν E P B f g G ∧ d < ds + t ∧ kr - t < HorizonExpanded N K 1 W ω ν E B f) ∧
  (∀ t : ℝ, 0 < t → ∃ a : ℝ, 0 < a ∧ ∀ N K L d W ω ν E P B f g G,
    Problem N K L d S η W ω ν E P B f g G → d < ds + a → HorizonExpanded N K L W ω ν E B f ≤ (kr + t) * L) ∧
  (∀ t : ℝ, 0 < t → ∃ a : ℝ, 0 < a ∧ ∀ N K L d W ω ν E P B f g G,
    Problem N K L d S η W ω ν E P B f g G → d < ds + a → (kr - a) * L < HorizonExpanded N K L W ω ν E B f →
    ∀ r : ℝ, 0 ≤ r → r ≤ L → |f r - f 0 - ds * r| ≤ t * L)

noncomputable def BoundedWidth : ℝ → ℝ → ℝ → ℝ → Prop :=
  fun ds kr S η =>
  ∃ a w : ℝ, 0 < a ∧ 0 ≤ w ∧ ∀ t : ℝ, 0 < t →
    ∃ N K d W ω ν E P B f g G,
    Problem N K 1 d S η W ω ν E P B f g G ∧ d < ds + t ∧ kr - t < HorizonExpanded N K 1 W ω ν E B f ∧
    ¬ NarrowTerminalExpanded N K 1 W ω ν E B f (kr + a) w

theorem terminalExpanded_iff (p : Data) (h : ℝ) :
    TerminalExpanded p.N p.K p.L p.W p.ω p.ν p.E p.B p.f h ↔ Terminal p h := by
  constructor
  · rintro ⟨M, D, hs⟩
    exact ⟨M, D, fun ε hε => (hs ε hε).mono fun k hk =>
      (terminalAt_iff_expanded p M D h ε k).mpr hk⟩
  · rintro ⟨M, D, hs⟩
    exact ⟨M, D, fun ε hε => (hs ε hε).mono fun k hk =>
      (terminalAt_iff_expanded p M D h ε k).mp hk⟩

theorem horizonExpanded_eq (p : Data) :
    HorizonExpanded p.N p.K p.L p.W p.ω p.ν p.E p.B p.f = horizon p := by
  unfold HorizonExpanded horizon
  congr 1
  ext h
  exact terminalExpanded_iff p h

end Submission.Obl.k4_critical_path_framework
