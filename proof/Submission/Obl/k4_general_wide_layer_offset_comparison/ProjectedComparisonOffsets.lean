import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedComparisonDecay
import Submission.Obl.k4_general_wide_layer_offset_comparison.BallOffsetFreezing

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ProjectedComparisonOffsets.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

noncomputable section

namespace ProjectedComparisonFrame

variable {α : Type} [MeasurableSpace α] {p : Parent α} {k : ℕ} {sc sf m H h g b : ℝ}
    {σ : Measure (α × ℝ)} (f : ProjectedComparisonFrame p k sc sf m H h g b σ)

/-- The original finite selectors determine one literal polynomial
difference. No choice of a new representative or resampled pair is involved. -/
def differencePolynomial (ω : α × ℝ) : MvPolynomial (Fin 3) ℝ :=
  f.fineAtlas.polynomial (f.fineAtlas.selector ω) -
    f.coarseAtlas.polynomial (f.coarseAtlas.selector ω)

theorem differencePolynomial_degree (ω : α × ℝ) :
    (f.differencePolynomial ω).totalDegree ≤ 2 :=
  (totalDegree_sub _ _).trans (max_le (f.fineAtlas.degree _) (f.coarseAtlas.degree _))

/-- Outside the original bad event the actual selected polynomial
difference is bounded on the entire real matching half ball. -/
theorem differencePolynomial_bound {ω : α × ℝ} {M : ℝ} (hω : ω ∉ f.bad M)
    (y : EuclideanSpace ℝ (Fin 3)) (hy : ‖y‖ ≤ 1 / 2) :
    |eval (fun i => y i) (f.differencePolynomial ω)| ≤ M := by
  have hsmall : ‖f.coarseAtlas.sheet (f.coarseAtlas.selector ω) (emb y) -
      f.fineAtlas.sheet (f.fineAtlas.selector ω) (emb y)‖ < M :=
    lt_of_not_ge (fun hle => hω ⟨y, hy, hle⟩)
  change ‖polynomialMatchSheet _ (emb y) - polynomialMatchSheet _ (emb y)‖ < M at hsmall
  rw [polynomialMatchSheet_real, polynomialMatchSheet_real, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at hsmall
  simpa only [differencePolynomial, eval_sub, abs_sub_comm] using hsmall.le

end ProjectedComparisonFrame

/-- Put the two physical chart coordinates into the real matching space;
the auxiliary matching coordinate can be fixed to zero after comparison. -/
def realMatchingPoint (x : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![x 0, x 1, 0]

theorem realMatchingPoint_norm_le (x : Fin 2 → ℝ) :
    ‖realMatchingPoint x‖ ≤ |x 0| + |x 1| := by
  have heq : ‖realMatchingPoint x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, realMatchingPoint, Fin.sum_univ_succ]
  have hnonneg := norm_nonneg (realMatchingPoint x)
  nlinarith [abs_nonneg (x 0), abs_nonneg (x 1),
    mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1)), sq_abs (x 0), sq_abs (x 1)]

theorem realMatchingPoint_dist_le (x y : Fin 2 → ℝ) :
    ‖realMatchingPoint x - realMatchingPoint y‖ ≤ |x 0 - y 0| + |x 1 - y 1| := by
  have heq : realMatchingPoint x - realMatchingPoint y = realMatchingPoint (x - y) := by
    ext i
    fin_cases i <;> simp [realMatchingPoint]
  rw [heq]
  exact realMatchingPoint_norm_le _

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
