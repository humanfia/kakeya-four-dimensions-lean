import Submission.Obl.k4_real_conic_restoration.Basic

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Submission.Obl.k4_real_conic_restoration

theorem triple_product_sub_bound {x y : Vec} {B δ : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hx : ∀ i, |x i| ≤ B) (hy : ∀ i, |y i| ≤ B)
    (hd : ∀ i, |x i - y i| ≤ δ) :
    |x 0 * x 1 * x 2 - y 0 * y 1 * y 2| ≤ 3 * B ^ 2 * δ := by
  have heq : x 0 * x 1 * x 2 - y 0 * y 1 * y 2 =
      (x 0 - y 0) * x 1 * x 2 + y 0 * (x 1 - y 1) * x 2 +
      y 0 * y 1 * (x 2 - y 2) := by ring
  have h0 : |(x 0 - y 0) * x 1 * x 2| ≤ B ^ 2 * δ := by
    simp only [abs_mul]
    calc
      _ ≤ δ * B * B := by gcongr; exact hd 0; exact hx 1; exact hx 2
      _ = _ := by ring
  have h1 : |y 0 * (x 1 - y 1) * x 2| ≤ B ^ 2 * δ := by
    simp only [abs_mul]
    calc
      _ ≤ B * δ * B := by gcongr; exact hy 0; exact hd 1; exact hx 2
      _ = _ := by ring
  have h2 : |y 0 * y 1 * (x 2 - y 2)| ≤ B ^ 2 * δ := by
    simp only [abs_mul]
    calc
      _ ≤ B * B * δ := by gcongr; exact hy 0; exact hy 1; exact hd 2
      _ = _ := by ring
  have h0' := abs_le.mp h0
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  rw [heq]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A uniform coordinate estimate for perturbing a three by three determinant. -/
theorem det_sub_bound {P Q : Mat} {B δ : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hP : ∀ i j, |P i j| ≤ B) (hQ : ∀ i j, |Q i j| ≤ B)
    (hd : ∀ i j, |P i j - Q i j| ≤ δ) :
    |P.det - Q.det| ≤ 18 * B ^ 2 * δ := by
  have ht (i j k l m n : Fin 3) :
      |P i j * P k l * P m n - Q i j * Q k l * Q m n| ≤ 3 * B ^ 2 * δ := by
    exact triple_product_sub_bound (x := ![P i j, P k l, P m n])
      (y := ![Q i j, Q k l, Q m n]) hB hδ
      (by intro a; fin_cases a <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> apply hP)
      (by intro a; fin_cases a <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> apply hQ)
      (by intro a; fin_cases a <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> apply hd)
  have h1 := abs_le.mp (ht 0 0 1 1 2 2)
  have h2 := abs_le.mp (ht 0 0 1 2 2 1)
  have h3 := abs_le.mp (ht 0 1 1 0 2 2)
  have h4 := abs_le.mp (ht 0 1 1 2 2 0)
  have h5 := abs_le.mp (ht 0 2 1 0 2 1)
  have h6 := abs_le.mp (ht 0 2 1 1 2 0)
  rw [Matrix.det_fin_three, Matrix.det_fin_three]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Submission.Obl.k4_real_conic_restoration
