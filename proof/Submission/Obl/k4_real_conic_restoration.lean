import Submission.Obl.k4_real_conic_restoration.RestoreFamily
set_option linter.unusedVariables false

/-!
# Quantitative restoration of a real conic

Five of the seven conditioned points give an explicit determinant lower bound
by changing projective coordinates. A spatial component of the gradient then
controls a one-coordinate real root correction. A polynomial bound for the
change of a three by three determinant preserves all triple floors.
-/

open Submission.Obl.k4_real_conic_restoration

theorem Submission.k4_real_conic_restoration : ∃ C : ℝ, 1 ≤ C ∧ ∀ A : ℝ, 2 ≤ A → ∀ (p : Fin 7 → EuclideanSpace ℝ (Fin 3)) (Q : Matrix (Fin 3) (Fin 3) ℝ) (ε : ℝ), (∀ i : Fin 7, p i 0 = 1 ∧ ‖p i‖ ≤ A) → (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → A⁻¹ ≤ |Matrix.det (Matrix.of fun a b : Fin 3 => (![p i, p j, p k] a) b)|) → Q.IsSymm → A⁻¹ ≤ (∑ a : Fin 3, ∑ b : Fin 3, |Q a b|) → (∑ a : Fin 3, ∑ b : Fin 3, |Q a b|) ≤ A → 0 ≤ ε → ε ≤ A ^ (-C) → (∀ i : Fin 7, |∑ a : Fin 3, ∑ b : Fin 3, p i a * Q a b * p i b| ≤ ε) → A ^ (-C) ≤ |Matrix.det Q| ∧ ∃ p' : Fin 7 → EuclideanSpace ℝ (Fin 3), (∀ i : Fin 7, p' i 0 = 1 ∧ (∑ a : Fin 3, ∑ b : Fin 3, p' i a * Q a b * p' i b) = 0 ∧ ‖p' i - p i‖ ≤ A ^ C * ε) ∧ (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → (2 * A)⁻¹ ≤ |Matrix.det (Matrix.of fun a b : Fin 3 => (![p' i, p' j, p' k] a) b)|) := by
  refine ⟨10000, by norm_num, ?_⟩
  intro A hA p Q ε hp htr hQ hQl hQu hε hs hq
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hpow : A ^ (10000 : ℝ) = A ^ (10000 : ℕ) := Real.rpow_natCast A 10000
  rw [Real.rpow_neg hA0.le, hpow] at hs
  have hs' : ε * A ^ 10000 ≤ 1 := by
    exact (mul_le_mul_of_nonneg_right hs (pow_nonneg hA0.le _)).trans_eq
      (inv_mul_cancel₀ (pow_ne_zero _ hA0.ne'))
  have hpa (i : Fin 7) (j : Fin 3) : |p i j| ≤ A := by
    have h : |p i j| ≤ ‖p i‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (p i) j
    exact h.trans (hp i).2
  have hqa (i j : Fin 3) : |Q i j| ≤ A := (entry_le_coeff Q i j).trans hQu
  have htr' (i j k : Fin 7) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      1 ≤ A * |(rows (p i) (p j) (p k)).det| := by
    have heq : (Matrix.of fun a b : Fin 3 => (![p i, p j, p k] a) b) =
        rows (p i) (p j) (p k) := by
      ext a b
      fin_cases a <;> rfl
    have ht := htr i j k hij hik hjk
    rw [heq] at ht
    simpa only [mul_comm] using (inv_le_iff_one_le_mul₀ hA0).mp ht
  have hQl' : 1 ≤ A * coeff Q := by
    simpa only [coeff, mul_comm] using (inv_le_iff_one_le_mul₀ hA0).mp hQl
  have hd := conditioned_det hA hpa htr' hQ hQl' hqa hε
    (small_power hA1 hε hs' (by norm_num : 1000 ≤ 10000)) hq
  constructor
  · rw [Real.rpow_neg hA0.le, hpow]
    apply (inv_le_iff_one_le_mul₀ (pow_pos hA0 10000)).mpr
    calc
      1 ≤ A ^ 760 * |Q.det| := hd
      _ ≤ A ^ 10000 * |Q.det| := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hA1 (by norm_num : 760 ≤ 10000)) (abs_nonneg _)
      _ = _ := by ring
  · obtain ⟨p', hp', htrp⟩ := restore_family hA (fun i => (hp i).1) hpa htr'
      hQ hqa hε hs' hq hd
    refine ⟨p', ?_, htrp⟩
    intro i
    refine ⟨(hp' i).1, (hp' i).2.1, ?_⟩
    rw [hpow]
    exact (hp' i).2.2.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hA1 (by norm_num : 771 ≤ 10000)) hε)
