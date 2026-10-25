import Submission.Obl.k4_scalar_grid_cartesian_field.Growth
import Submission.Obl.k4_scalar_grid_cartesian_field.PreparationNumerics

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Filter

/-- A single subpower sequence covers every explicit outer loss and both slow accuracies. -/
theorem exists_preparation_envelope {N K H₀ H L X Y : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : SubpowerLoss N K) (hH₀ : SubpowerLoss N H₀) (hH : SubpowerLoss N H)
    (hL : SubpowerLoss N L) (hX : SubpowerLoss N X) (hY : SubpowerLoss N Y) :
    ∃ Λ : ℕ → ℝ, SubpowerLoss N Λ ∧ ∀ k,
      PreparationBudgetBounds (K k) (L k) (H₀ k) (H k) (Λ k) ∧ X k ≤ Λ k ∧ Y k ≤ Λ k := by
  let W : ℕ → ℝ := fun k => max (K k) (max (H₀ k) (max (L k) (max (H k) (max (X k) (Y k)))))
  have hW : SubpowerLoss N W :=
    Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max hK
      (Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max hH₀
        (Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max hL
          (Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max hH
            (Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max hX hY))))
  let Λ : ℕ → ℝ := fun k => preparationBudget (W k)
  have hΛ : SubpowerLoss N Λ :=
    Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_polynomial hN hNt hW
      (by norm_num : (1 : ℝ) ≤ 1000000000) 20
  refine ⟨Λ, hΛ, fun k => ?_⟩
  have hKW : K k ≤ W k := le_max_left _ _
  have hH₀W : H₀ k ≤ W k := le_max_of_le_right (le_max_left _ _)
  have hLW : L k ≤ W k := le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hHW : H k ≤ W k := le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have hXW : X k ≤ W k := le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_left _ _))))
  have hYW : Y k ≤ W k := le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_right _ _))))
  have hWΛ : W k ≤ Λ k := (preparationBudget_base (hW.1 k)).2
  exact ⟨preparationBudget_bounds (hK.1 k) (hL.1 k) (hH₀.1 k) (hH.1 k) hKW hLW hH₀W hHW,
    hXW.trans hWΛ, hYW.trans hWΛ⟩

end Submission.Obl.k4_scalar_grid_cartesian_field
