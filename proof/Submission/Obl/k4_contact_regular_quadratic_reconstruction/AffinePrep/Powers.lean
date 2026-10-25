import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.CoreBudget

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep

open Submission.Lib.K4QuadraticSheetCore

noncomputable section

/-- The accepted core budget becomes a pure power after enlarging the
subpower envelope by one fixed constant. `cubeErr` is definitionally the
`coreLoss` used by the second affine preparation. -/
theorem cube_error_power_budget (Cs : ℝ) (hCs : 0 < Cs) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ Λ ε ρ : ℝ, A ≤ Λ → 0 ≤ ε → 0 ≤ ρ →
      Submission.Obl.k4_contact_fine_labels_from_coarse_cover.cubeErr Cs Λ ≤ Λ ^ (81 : ℕ) ∧
      (Λ ^ (81 : ℕ) * (ε + ρ) ≤ 1 →
        4 * Cs * remezC 4 Λ * ρ ≤ 1 ∧
        8 * discBudget Cs Λ * ρ * Λ ^ 2 ≤ 1 ∧
        192 * Cs * sffKappa Cs Λ * (ε + ρ) * Λ ^ 2 ≤ 1) := by
  obtain ⟨A, hA, hbudget⟩ :=
    Submission.Obl.k4_contact_fine_labels_from_coarse_cover.core_budgets Cs hCs
  refine ⟨A, hA, ?_⟩
  intro Λ ε ρ hAΛ hε hρ
  have hΛ : 1 ≤ Λ := hA.trans hAΛ
  obtain ⟨hloss, hsmall⟩ := hbudget Λ ε ρ hΛ hε hρ
  have hpower : A * Λ ^ (80 : ℕ) ≤ Λ ^ (81 : ℕ) := by
    calc
      A * Λ ^ (80 : ℕ) ≤ Λ * Λ ^ (80 : ℕ) :=
        mul_le_mul_of_nonneg_right hAΛ (by positivity)
      _ = _ := by ring
  refine ⟨hloss.trans hpower, ?_⟩
  intro hsm
  exact hsmall ((mul_le_mul_of_nonneg_right hpower (add_nonneg hε hρ)).trans hsm)

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep
