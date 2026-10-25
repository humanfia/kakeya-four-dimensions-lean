import Mathlib

namespace Submission.Obl.k4_algebraic_sheet_remez

/-- Increase the coefficient and exponent to obtain the common-constant form
used in the Remez conclusion. -/
theorem exists_common_power_constant (A : ℝ) (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ θ V : ℝ, 0 < θ → θ ≤ 1 → 0 ≤ V →
      A * (θ ^ k)⁻¹ * V ≤ C * θ ^ (-C) * V := by
  let C := max 1 (max A (k : ℝ))
  have hAC : A ≤ C := (le_max_left A (k : ℝ)).trans (le_max_right 1 _)
  have hkC : (k : ℝ) ≤ C := (le_max_right A (k : ℝ)).trans (le_max_right 1 _)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro θ V hθ hθ1 hV
  have hpow : (θ ^ k)⁻¹ ≤ θ ^ (-C) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hθ.le]
    exact Real.rpow_le_rpow_of_exponent_ge hθ hθ1 (neg_le_neg hkC)
  apply mul_le_mul_of_nonneg_right _ hV
  calc
    _ ≤ C * (θ ^ k)⁻¹ := mul_le_mul_of_nonneg_right hAC (by positivity)
    _ ≤ C * θ ^ (-C) := mul_le_mul_of_nonneg_left hpow (by dsimp [C]; positivity)

end Submission.Obl.k4_algebraic_sheet_remez
