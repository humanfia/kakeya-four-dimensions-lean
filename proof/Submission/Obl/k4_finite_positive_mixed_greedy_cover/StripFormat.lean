import Submission.Obl.k4_finite_positive_mixed_greedy_cover.Interface
import Submission.Obl.k4_quadratic_finite_greedy_cover.EligibilityFormat

namespace Submission.Obl.k4_finite_positive_mixed_greedy_cover

open MeasureTheory Set MvPolynomial
open scoped ENNReal
noncomputable section

private def velIndex (e : Fin 2) : Fin 6 := ⟨e.val + 3, by omega⟩

private def stripPoly (T : ℕ) (u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (a : Fin 2 → ℝ) (z : ℝ) : MvPolynomial (Fin 6) ℝ :=
  (∑ e, C (a e * ((2 : ℝ) ^ T)⁻¹) *
    (∑ f, C (Q⁻¹ e f) * (X (velIndex f) - C (u f)))) - C z

private theorem stripPoly_degree (T : ℕ) (u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (a : Fin 2 → ℝ) (z : ℝ) :
    (stripPoly T u Q a z).totalDegree ≤ 1 := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply totalDegree_finsetSum_le
    intro e he
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    apply totalDegree_finsetSum_le
    intro f hf
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    exact (totalDegree_sub _ _).trans (by simp)
  · simp

private theorem stripPoly_eval (T : ℕ) (u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (a : Fin 2 → ℝ) (z : ℝ)
    (q : ℕ) (w : Fin 6 → ℝ) :
    eval w (stripPoly T u Q a z) =
      (∑ e, a e * ((2 : ℝ) ^ T)⁻¹ * (Matrix.toEuclideanLin Q⁻¹ (v (q,w) - u)) e) - z := by
  have hv (f : Fin 2) : (v (q,w)) f = w (velIndex f) := by
    fin_cases f <;> simp [v, Submission.Obl.k4_quadratic_finite_greedy_cover.v, velIndex]
  simp [stripPoly, Matrix.toEuclideanLin, Matrix.toLpLin_apply, hv]

/-- An actual old-frame velocity strip needs only two affine sign tests. -/
theorem strip_format (T : ℕ) (u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (a : Fin 2 → ℝ) (z width : ℝ) (q : ℕ) :
    fmt 6 2 1 {w | InStrip T u Q a z width (q,w)} := by
  classical
  let P := stripPoly T u Q a z
  refine ⟨2, by norm_num, ![C width + P, C width - P], ?_, fun b => b 0 && b 1, ?_⟩
  · intro i
    fin_cases i
    · change (C width + P).totalDegree ≤ 1
      exact (totalDegree_add (C width) P).trans (max_le (by simp) (stripPoly_degree T u Q a z))
    · change (C width - P).totalDegree ≤ 1
      exact (totalDegree_sub (C width) P).trans (max_le (by simp) (stripPoly_degree T u Q a z))
  · intro w
    simp only [mem_ofPred_eq, InStrip, Bool.and_eq_true, Matrix.cons_val_zero,
      Matrix.cons_val_one, eval_add, eval_C, map_sub, decide_eq_true_eq]
    rw [show eval w P = _ from stripPoly_eval T u Q a z q w]
    simp only [map_sub]
    exact abs_le.trans (by constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith)

/-- Strip eligibility is measurable in the original trajectory labels. -/
theorem strip_measurable (T : ℕ) (u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (a : Fin 2 → ℝ) (z width : ℝ) :
    MeasurableSet {l : ℕ × (Fin 6 → ℝ) | InStrip T u Q a z width l} := by
  have heq : {l : ℕ × (Fin 6 → ℝ) | InStrip T u Q a z width l} =
      ⋃ q : ℕ, ({q} ×ˢ {w | InStrip T u Q a z width (q,w)}) := by
    ext ⟨q,w⟩
    simp
  rw [heq]
  exact MeasurableSet.iUnion (fun q => (show MeasurableSet ({q} : Set ℕ) from measurableSet_singleton q).prod
    (Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.measurableSet (strip_format T u Q a z width q)))

end
end Submission.Obl.k4_finite_positive_mixed_greedy_cover
