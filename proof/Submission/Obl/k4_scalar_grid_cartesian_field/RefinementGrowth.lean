import Submission.Obl.k4_scalar_grid_cartesian_field.SourceRefinement

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Filter

/-- The fine-cell count budget is subpower before the angular mesh is chosen. -/
theorem fineCellBudget_subpower {N K L H₀ : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k)
    (hNt : Tendsto N atTop atTop) (hK : SubpowerLoss N K) (hL : SubpowerLoss N L)
    (hH₀ : SubpowerLoss N H₀) : SubpowerLoss N (fun k => fineCellBudget (K k) (L k) (H₀ k)) := by
  have hNpos : ∀ k, 0 < N k := fun k => zero_lt_one.trans_le (hN k)
  have hL₃ := Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_polynomial
    hN hNt hL (by norm_num : (1 : ℝ) ≤ 8000) 3
  have hH₄ : SubpowerLoss N (fun k => H₀ k ^ 4) := by
    simpa only [one_mul] using Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_polynomial
      hN hNt hH₀ (show (1 : ℝ) ≤ 1 from le_rfl) 4
  exact Submission.Obl.k4_tempered_grid_selection.subpower_mul hNpos
    (Submission.Obl.k4_tempered_grid_selection.subpower_mul hNpos hL₃ hH₄) hK

/-- The restored palette constant is subpower independently of the eventual separation width. -/
theorem sourcePaletteBudget_subpower {N K L H₀ H : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k)
    (hNt : Tendsto N atTop atTop) (hK : SubpowerLoss N K) (hL : SubpowerLoss N L)
    (hH₀ : SubpowerLoss N H₀) (hH : SubpowerLoss N H) :
    SubpowerLoss N (fun k => sourcePaletteBudget (K k) (L k) (H₀ k) (H k)) := by
  have hNpos : ∀ k, 0 < N k := fun k => zero_lt_one.trans_le (hN k)
  have hJ := fineCellBudget_subpower hN hNt hK hL hH₀
  have hprod := Submission.Obl.k4_tempered_grid_selection.subpower_mul hNpos
    (Submission.Obl.k4_tempered_grid_selection.subpower_mul hNpos hK hJ) hH
  have hp := Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_polynomial hN hNt hprod
    (by norm_num : (1 : ℝ) ≤ 32) 1
  simpa only [sourcePaletteBudget, pow_one, mul_assoc] using hp

end Submission.Obl.k4_scalar_grid_cartesian_field
