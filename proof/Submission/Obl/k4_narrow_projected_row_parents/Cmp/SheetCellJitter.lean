/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/SheetCellJitter.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.MeshPairLaw
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetGroupMatching

/-! Agreement at an original point survives resampling inside a sufficiently small cell. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Metric Set

noncomputable section

/-- Agreement on a stable ball is measurable for finite lists of sheets. -/
theorem measurableSet_pair_sheet_close {D n₁ n₂ : ℕ}
    (f₁ : Fin n₁ → EuclideanSpace ℂ (Fin 3) → ℂ)
    (f₂ : Fin n₂ → EuclideanSpace ℂ (Fin 3) → ℂ)
    (hs₁ : ∀ i, IsSheet D (f₁ i)) (hs₂ : ∀ j, IsSheet D (f₂ j))
    {r : ℝ} (hr : r < 4) (a : ℝ) :
    MeasurableSet {p : (Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3) |
      ‖p.2‖ ≤ r ∧ ‖f₁ p.1.1 (emb p.2) - f₂ p.1.2 (emb p.2)‖ ≤ a} := by
  have heq : {p : (Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3) |
      ‖p.2‖ ≤ r ∧ ‖f₁ p.1.1 (emb p.2) - f₂ p.1.2 (emb p.2)‖ ≤ a} =
      ⋃ i, ⋃ j, {(i, j)} ×ˢ {x : EuclideanSpace ℝ (Fin 3) |
        ‖x‖ ≤ r ∧ ‖f₁ i (emb x) - f₂ j (emb x)‖ ≤ a} := by
    ext p
    rcases p with ⟨⟨i, j⟩, x⟩
    simp
  rw [heq]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
    (measurableSet_singleton (i, j)).prod
      (measurableSet_norm_le_of_continuousOn (continuousOn_sheet_sub (hs₁ i) (hs₂ j) hr))

/-- Resampling inside a small cell preserves both the stable margin and agreement. -/
theorem sheet_close_on_cell
    (f g : EuclideanSpace ℝ (Fin 3) → ℂ) (K : NNReal) {δ a : ℝ}
    (hδ : δ ≤ 1 / 8) (hsmall : 2 * (K : ℝ) * δ ≤ a / 2)
    (hf : LipschitzOnWith K f (closedBall 0 (1 / 2)))
    (hg : LipschitzOnWith K g (closedBall 0 (1 / 2)))
    {x y : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ ≤ 1 / 8)
    (hxy : dist y x ≤ δ) (hclose : ‖f x - g x‖ ≤ a / 2) :
    ‖y‖ ≤ 1 / 4 ∧ ‖f y - g y‖ ≤ a := by
  have hy : ‖y‖ ≤ 1 / 4 := by
    have hn : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
      calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    rw [dist_eq_norm] at hxy
    linarith
  have hx' : x ∈ closedBall 0 (1 / 2) := by rw [mem_closedBall_zero_iff]; linarith
  have hy' : y ∈ closedBall 0 (1 / 2) := by rw [mem_closedBall_zero_iff]; linarith
  have hf' : ‖f y - f x‖ ≤ (K : ℝ) * δ := by
    calc ‖f y - f x‖ = dist (f y) (f x) := (dist_eq_norm _ _).symm
      _ ≤ (K : ℝ) * dist y x := hf.dist_le_mul y hy' x hx'
      _ ≤ _ := mul_le_mul_of_nonneg_left hxy K.coe_nonneg
  have hg' : ‖g x - g y‖ ≤ (K : ℝ) * δ := by
    calc ‖g x - g y‖ = dist (g x) (g y) := (dist_eq_norm _ _).symm
      _ ≤ (K : ℝ) * dist x y := hg.dist_le_mul x hx' y hy'
      _ = (K : ℝ) * dist y x := by rw [dist_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hxy K.coe_nonneg
  refine ⟨hy, ?_⟩
  have ht₁ := dist_triangle (f y) (f x) (g y)
  have ht₂ := dist_triangle (f x) (g x) (g y)
  simp only [dist_eq_norm] at ht₁ ht₂
  linarith

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
