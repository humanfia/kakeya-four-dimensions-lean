import Mathlib

namespace Submission.Obl.k4_conditional_common_affine_field

noncomputable def affineOfAxes (β : Fin 4 → ℝ) (c v₀ w₁ w₂ : ℝ) : Fin 4 → ℝ :=
  ![β 0,-β 1*(w₁-v₀)-β 2*(w₂-v₀),β 1+β 2,c]

theorem affineOfAxes_identity (β : Fin 4 → ℝ) (c v₀ w₁ w₂ t Y : ℝ) :
    affineOfAxes β c v₀ w₁ w₂ 0+affineOfAxes β c v₀ w₁ w₂ 1*t+
      affineOfAxes β c v₀ w₁ w₂ 2*Y =
        β 0+β 1*(Y-t*(w₁-v₀))+β 2*(Y-t*(w₂-v₀)) := by
  dsimp [affineOfAxes]
  ring

theorem affineOfAxes_bound (β : Fin 4 → ℝ) (c v₀ w₁ w₂ J H : ℝ)
    (hJ : 0 ≤ J) (hH : 1 ≤ H) (hβ : ∀ i, |β i| ≤ J) (hc : |c| ≤ J)
    (hw₁ : |w₁-v₀| ≤ H) (hw₂ : |w₂-v₀| ≤ H) :
    ∀ i, |affineOfAxes β c v₀ w₁ w₂ i| ≤ 4*J*H := by
  have hH0 : 0 ≤ H := by linarith
  have hJH : J ≤ J*H := by nlinarith
  have hprod₁ : |β 1*(w₁-v₀)| ≤ J*H := by
    rw [abs_mul]
    exact mul_le_mul (hβ 1) hw₁ (abs_nonneg _) hJ
  have hprod₂ : |β 2*(w₂-v₀)| ≤ J*H := by
    rw [abs_mul]
    exact mul_le_mul (hβ 2) hw₂ (abs_nonneg _) hJ
  intro i
  fin_cases i
  · change |β 0| ≤ 4*J*H
    nlinarith [hβ 0]
  · change |-β 1*(w₁-v₀)-β 2*(w₂-v₀)| ≤ 4*J*H
    have h := (abs_sub (-β 1*(w₁-v₀)) (β 2*(w₂-v₀))).trans
      (add_le_add (by simpa only [neg_mul,abs_neg] using hprod₁) hprod₂)
    nlinarith
  · change |β 1+β 2| ≤ 4*J*H
    have h := (abs_add_le _ _).trans (add_le_add (hβ 1) (hβ 2))
    nlinarith
  · change |c| ≤ 4*J*H
    nlinarith

/-- Removing a small mixed coefficient costs its bound times the squared
intercept radius. This estimate applies on the whole fitted event. -/
theorem erase_mixed_error (F β₀ β₁ β₂ β₃ x y B r Q E : ℝ)
    (hr : 0 < r) (hB : 0 ≤ B) (hx : |x| ≤ B) (hy : |y| ≤ B)
    (hβ : |β₃| * r^2 ≤ Q)
    (hfit : |F-(β₀+β₁*x+β₂*y+β₃*x*y)| ≤ E) :
    |F-(β₀+β₁*x+β₂*y)| ≤ E+Q*B^2/r^2 := by
  have hr2 : 0 < r^2 := sq_pos_of_pos hr
  have hQ : 0 ≤ Q := (mul_nonneg (abs_nonneg _) (sq_nonneg _)).trans hβ
  have hβ' : |β₃| ≤ Q/r^2 := (le_div_iff₀ hr2).mpr hβ
  have hxy : |x| * |y| ≤ B^2 := by
    simpa only [pow_two] using mul_le_mul hx hy (abs_nonneg _) hB
  have hterm : |β₃*x*y| ≤ Q*B^2/r^2 := by
    rw [abs_mul,abs_mul]
    calc
      _ = |β₃| * (|x| * |y|) := by ring
      _ ≤ (Q/r^2)*B^2 := mul_le_mul hβ' hxy (by positivity) (by positivity)
      _ = _ := by ring
  have hid : F-(β₀+β₁*x+β₂*y) =
      (F-(β₀+β₁*x+β₂*y+β₃*x*y))+β₃*x*y := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hfit hterm)

end Submission.Obl.k4_conditional_common_affine_field
