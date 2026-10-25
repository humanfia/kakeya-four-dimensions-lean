import Submission.Obl.k4_critical_intercept_concentration.SwitchingModel
import Submission.Obl.k4_critical_switching_state_preparation
import Submission.Obl.k4_horizontal_three_traversal_spreading

namespace Submission.Obl.k4_critical_intercept_concentration

noncomputable section

/-- The matching input of the frozen parent, retained in the preparation child. -/
def Match : Prop := ((∀ (D J : ℕ), 1 ≤ D → D < J → ∀ d : ℝ, 0 ≤ d → d < 1 → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)), (n₁ : ℝ) ≤ N ^ (d + η) → (n₂ : ℝ) ≤ N ^ (d + η) → (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) → (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) → (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₁ i) t| ≤ N ^ η) → (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv j (f₂ i) t| ≤ N ^ η) → (∀ i : Fin n₁, 0 ≤ π₁ i) → (∀ i : Fin n₂, 0 ≤ π₂ i) → (∑ i : Fin n₁, π₁ i) = 1 → (∑ i : Fin n₂, π₂ i) = 1 → MeasureTheory.IsProbabilityMeasure μ → (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E → μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ i) * MeasureTheory.volume E) → (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E → μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ i) * MeasureTheory.volume E) → ¬ μ {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + η) ∧ ∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ N ^ (-η) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|}ᶜ = 0))

/-- Definitional adapter from the expanded Mathlib-only geometric child. -/
theorem local_spreading : LocalSpreading :=
  Submission.k4_horizontal_three_traversal_spreading

/-- Convert the expanded Mathlib-only model fields to the named local data.
No hypothesis or original reference weight is changed. -/
theorem switching_preparation (hm : Match) : SwitchingPreparation := by
  intro α _ cfg h
  exact Submission.k4_critical_switching_state_preparation hm cfg.N cfg.K
    h.scale h.scale_limit h.subpower cfg.d cfg.κ cfg.ℓ cfg.S cfg.U cfg.e₀
    h.dimension_nonneg h.dimension_lt_one h.rate_pos h.rate_le_one h.transverse_pos
    h.palette_pos h.palette_le_one h.depth_pos h.defect_pos h.critical_rate
    (fun _ => h.horizontal_rate) α cfg.ν cfg.μ cfg.ρ cfg.π cfg.b cfg.P cfg.T cfg.n
    cfg.j cfg.A cfg.B cfg.c cfg.F h.basic h.caps h.atlas h.nested

end

end Submission.Obl.k4_critical_intercept_concentration
