import Mathlib

/-!
# Three-point bound for quadratics

Adapted from: here:o078 (session x0262, `QuadBounds.lean` on o078's branch x0262).
-/

namespace Submission.Lib.K4QuadSheetMatching

/-- Lagrange interpolation at three separated points bounds a quadratic everywhere. -/
theorem quad_three_point_bound {a b c A δ x₁ x₂ x₃ : ℝ} (hδ : 0 < δ)
    (h12 : x₁ + δ ≤ x₂) (h23 : x₂ + δ ≤ x₃)
    (h₁ : |a + b * x₁ + c * x₁ ^ 2| ≤ A) (h₂ : |a + b * x₂ + c * x₂ ^ 2| ≤ A)
    (h₃ : |a + b * x₃ + c * x₃ ^ 2| ≤ A) (x : ℝ) :
    |a + b * x + c * x ^ 2| ≤ 3 * A * ((|x - x₁| + (x₃ - x₁)) / δ) ^ 2 := by
  set p : ℝ → ℝ := fun z => a + b * z + c * z ^ 2 with hp
  have hd12 : x₁ - x₂ ≠ 0 := by intro h; linarith
  have hd13 : x₁ - x₃ ≠ 0 := by intro h; linarith
  have hd23 : x₂ - x₃ ≠ 0 := by intro h; linarith
  have hlag : p x = p x₁ * ((x - x₂) * (x - x₃) / ((x₁ - x₂) * (x₁ - x₃))) +
      p x₂ * ((x - x₁) * (x - x₃) / ((x₂ - x₁) * (x₂ - x₃))) +
      p x₃ * ((x - x₁) * (x - x₂) / ((x₃ - x₁) * (x₃ - x₂))) := by
    have hd21 : x₂ - x₁ ≠ 0 := by intro h; linarith
    have hd31 : x₃ - x₁ ≠ 0 := by intro h; linarith
    have hd32 : x₃ - x₂ ≠ 0 := by intro h; linarith
    simp only [hp]
    field_simp
    ring
  set R := |x - x₁| + (x₃ - x₁) with hR
  have hA : 0 ≤ A := le_trans (abs_nonneg _) h₁
  have hRnn : 0 ≤ R := by rw [hR]; have := abs_nonneg (x - x₁); linarith
  -- each Lagrange factor is bounded by `(R / δ) ^ 2`
  have hfac : ∀ u v w z : ℝ, |u| ≤ R → |v| ≤ R → δ ≤ |w| → δ ≤ |z| →
      |u * v / (w * z)| ≤ (R / δ) ^ 2 := by
    intro u v w z hu hv hw hz
    have hw0 : 0 < |w| := lt_of_lt_of_le hδ hw
    have hz0 : 0 < |z| := lt_of_lt_of_le hδ hz
    rw [abs_div, abs_mul, abs_mul, div_pow, div_le_div_iff₀ (mul_pos hw0 hz0) (by positivity)]
    calc |u| * |v| * δ ^ 2 ≤ R * R * δ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul hu hv (abs_nonneg _) hRnn
      _ ≤ R ^ 2 * (|w| * |z|) := by
          rw [sq, sq]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hw hz hδ.le (abs_nonneg _)
  have hxx1 : |x - x₁| ≤ R := by rw [hR]; linarith
  have hxx2 : |x - x₂| ≤ R := by
    rw [hR]
    calc |x - x₂| = |(x - x₁) + (x₁ - x₂)| := by ring_nf
      _ ≤ |x - x₁| + |x₁ - x₂| := abs_add_le _ _
      _ ≤ |x - x₁| + (x₃ - x₁) := by
          have : |x₁ - x₂| = x₂ - x₁ := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
          rw [this]; linarith
  have hxx3 : |x - x₃| ≤ R := by
    rw [hR]
    calc |x - x₃| = |(x - x₁) + (x₁ - x₃)| := by ring_nf
      _ ≤ |x - x₁| + |x₁ - x₃| := abs_add_le _ _
      _ = |x - x₁| + (x₃ - x₁) := by
          rw [abs_sub_comm x₁ x₃, abs_of_nonneg (show (0:ℝ) ≤ x₃ - x₁ by linarith)]
  have hsep : ∀ u v : ℝ, u + δ ≤ v → δ ≤ |u - v| ∧ δ ≤ |v - u| := by
    intro u v huv
    constructor
    · rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  have h13 : x₁ + δ ≤ x₃ := by linarith
  have e1 := hfac _ _ _ _ hxx2 hxx3 (hsep _ _ h12).1 (hsep _ _ h13).1
  have e2 := hfac _ _ _ _ hxx1 hxx3 (hsep _ _ h12).2 (hsep _ _ h23).1
  have e3 := hfac _ _ _ _ hxx1 hxx2 (hsep _ _ h13).2 (hsep _ _ h23).2
  show |p x| ≤ 3 * A * (R / δ) ^ 2
  rw [hlag]
  have t1 : |p x₁ * ((x - x₂) * (x - x₃) / ((x₁ - x₂) * (x₁ - x₃)))| ≤ A * (R / δ) ^ 2 := by
    rw [abs_mul]; exact mul_le_mul h₁ e1 (abs_nonneg _) hA
  have t2 : |p x₂ * ((x - x₁) * (x - x₃) / ((x₂ - x₁) * (x₂ - x₃)))| ≤ A * (R / δ) ^ 2 := by
    rw [abs_mul]; exact mul_le_mul h₂ e2 (abs_nonneg _) hA
  have t3 : |p x₃ * ((x - x₁) * (x - x₂) / ((x₃ - x₁) * (x₃ - x₂)))| ≤ A * (R / δ) ^ 2 := by
    rw [abs_mul]; exact mul_le_mul h₃ e3 (abs_nonneg _) hA
  calc _ ≤ |p x₁ * ((x - x₂) * (x - x₃) / ((x₁ - x₂) * (x₁ - x₃)))| +
        |p x₂ * ((x - x₁) * (x - x₃) / ((x₂ - x₁) * (x₂ - x₃)))| +
        |p x₃ * ((x - x₁) * (x - x₂) / ((x₃ - x₁) * (x₃ - x₂)))| := abs_add_three _ _ _
    _ ≤ A * (R / δ) ^ 2 + A * (R / δ) ^ 2 + A * (R / δ) ^ 2 := by linarith
    _ = 3 * A * (R / δ) ^ 2 := by ring

end Submission.Lib.K4QuadSheetMatching
