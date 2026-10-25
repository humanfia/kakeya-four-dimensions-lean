import Mathlib

namespace Submission.Obl.k4_true_forest_own_depth_preparation

/-- Sum a finite forest by its levels. -/
theorem sum_over_levels {C m : ℕ} (lev : Fin C → ℕ) (hlev : ∀ b, lev b < m)
    (mass : Fin C → ENNReal) :
    (∑ i : Fin m, ∑ b, if lev b = i.val then mass b else 0) = ∑ b, mass b := by
  classical
  let levFin : Fin C → Fin m := fun b => ⟨lev b, hlev b⟩
  simpa only [Finset.sum_filter, levFin, Fin.ext_iff] using
    Finset.sum_fiberwise Finset.univ levFin mass

/-- Uniform layer bounds sum with only a factor from the fixed forest depth. -/
theorem sum_le_depth_mul {C m : ℕ} (lev : Fin C → ℕ) (hlev : ∀ b, lev b < m)
    (mass : Fin C → ENNReal) (B : ENNReal)
    (hB : ∀ i, i < m → (∑ b, if lev b = i then mass b else 0) ≤ B) :
    (∑ b, mass b) ≤ (m : ENNReal) * B := by
  rw [← sum_over_levels lev hlev mass]
  calc
    _ ≤ ∑ _i : Fin m, B := Finset.sum_le_sum fun i _ => hB i.val i.isLt
    _ = _ := by simp [nsmul_eq_mul]

end Submission.Obl.k4_true_forest_own_depth_preparation
