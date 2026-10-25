import Submission.Obl.k4_horizontal_coefficient_count.LMCluster
import Submission.Obl.k4_horizontal_coefficient_count.HeavyBins

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set

variable {α : Type} [MeasurableSpace α]

theorem lmCode_eq_horizontalCode (χ a : ℝ) (β : Fin 6 → ℝ) :
    lmCode χ a β = horizontalCode χ a β := rfl

theorem lmCell_eq_horizontalCell (b : α → Fin 6 → ℝ) (G : Set α)
    (χ a : ℝ) (q : Fin 5 → ℤ) :
    lmCell b χ a G q = horizontalCell b G χ a q := rfl

theorem lmWeight_eq_codeWeight (π : Measure ℝ) (χ a d Z : ℝ) (q : Fin 5 → ℤ) :
    lmWeight π χ a d Z q = codeWeight π χ a d Z q := rfl

/-- The analytic light labels and the predictor constructor's light
incidences use the same original palette-weighted threshold. -/
theorem lightCells_eq_lmLight (μ : Measure (α × ℝ)) (π : Measure ℝ)
    (b : α → Fin 6 → ℝ) (G : Set α) (χ a d Z : ℝ) :
    lightCells μ π b G χ a d Z = lmLight μ π b χ a d Z G ×ˢ univ := by
  ext p
  simp only [lightCells, lmLight, lmCell_eq_horizontalCell, lmWeight_eq_codeWeight,
    lmCode_eq_horizontalCode, mem_setOf_eq, mem_prod, mem_univ, and_true]

end Submission.Obl.k4_horizontal_coefficient_count
