import Mathlib
/- Adapted from same-tree o231/x0798 fbdba9e7, Cons/Geometry.lean.
Only the geometric data used by heavy intercept selection are retained. -/
namespace Submission.Obl.k4_scalar_heavy_intercept_selection.Cons
open MeasureTheory
noncomputable section

def yL (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) : ℝ := l.2 0 + t * l.2 1

def xL (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) : ℝ := l.2 2 + t * l.2 3 + t ^ 2 * l.2 4

def ubase (z₀ : Fin 2 → ℝ) (h : ℝ) (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) : Fin 2 → ℝ :=
  fun e => ((![t, yL l t] : Fin 2 → ℝ) e - z₀ e) / h

theorem ubase_one (z₀ : Fin 2 → ℝ) (h : ℝ) (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) :
    ubase z₀ h l t 1 = (yL l t - z₀ 1) / h := by
  simp [ubase]

def physState (δs : ℝ) (p : (ℕ × (Fin 5 → ℝ)) × ℝ) : Fin 3 → ℤ :=
  fun e => ⌊(![p.2, yL p.1 p.2, xL p.1 p.2] : Fin 3 → ℝ) e / δs⌋

theorem measurable_physState (δs : ℝ) : Measurable (physState δs) := by
  apply measurable_pi_iff.mpr
  intro e
  fin_cases e <;> simp only [physState, yL, xL, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;> fun_prop

end
end Submission.Obl.k4_scalar_heavy_intercept_selection.Cons
