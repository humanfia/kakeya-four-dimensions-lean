import Submission.Obl.k4_real_conic_restoration.Shift
import Submission.Obl.k4_real_conic_restoration.Perturbation

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Submission.Obl.k4_real_conic_restoration

/-- Simultaneous correction, retaining half of every triple determinant floor. -/
theorem restore_family {p : Fin 7 → EuclideanSpace ℝ (Fin 3)} {Q : Mat} {A ε : ℝ}
    (hA : 2 ≤ A) (hp0 : ∀ i, p i 0 = 1) (hp : ∀ i j, |p i j| ≤ A)
    (hdet : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      1 ≤ A * |(rows (p i) (p j) (p k)).det|)
    (hQ : Q.IsSymm) (hQu : ∀ i j, |Q i j| ≤ A)
    (hε : 0 ≤ ε) (hs : ε * A ^ 10000 ≤ 1) (hq : ∀ i, |quad Q (p i)| ≤ ε)
    (hd : 1 ≤ A ^ 760 * |Q.det|) :
    ∃ p' : Fin 7 → EuclideanSpace ℝ (Fin 3),
      (∀ i, p' i 0 = 1 ∧ quad Q (p' i) = 0 ∧ ‖p' i - p i‖ ≤ A ^ 771 * ε) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        (2 * A)⁻¹ ≤ |(rows (p' i) (p' j) (p' k)).det|) := by
  classical
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  choose p' hp' using fun i => restore_point hA hε hs (hp0 i) (hp i) hQ hQu (hq i) hd
  refine ⟨p', hp', ?_⟩
  let δ : ℝ := A ^ 771 * ε
  have hδ : 0 ≤ δ := mul_nonneg (pow_nonneg hA0.le _) hε
  have hδsmall : δ ≤ 1 := by
    dsimp [δ]
    simpa only [mul_comm] using small_power hA1 hε hs (by decide : 771 ≤ 10000)
  have hdiff (i : Fin 7) (j : Fin 3) : |p' i j - p i j| ≤ δ := by
    have h := PiLp.norm_apply_le (p' i - p i) j
    have hh : |p' i j - p i j| ≤ ‖p' i - p i‖ := by simpa only [Real.norm_eq_abs, PiLp.sub_apply] using h
    exact hh.trans (hp' i).2.2
  have hnew (i : Fin 7) (j : Fin 3) : |p' i j| ≤ 2 * A := by
    have hh : |p' i j| ≤ |p' i j - p i j| + |p i j| := by
      calc
        _ = |(p' i j - p i j) + p i j| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    linarith [hdiff i j, hp i j]
  have hold (i : Fin 7) (j : Fin 3) : |p i j| ≤ 2 * A := by linarith [hp i j]
  intro i j k hij hik hjk
  let P : Mat := rows (p' i) (p' j) (p' k)
  let R : Mat := rows (p i) (p j) (p k)
  have hPr : ∀ a b, |P a b| ≤ 2 * A := by
    intro a b
    fin_cases a <;> simp only [P, rows, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two] <;> apply hnew
  have hRr : ∀ a b, |R a b| ≤ 2 * A := by
    intro a b
    fin_cases a <;> simp only [R, rows, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two] <;> apply hold
  have hPR : ∀ a b, |P a b - R a b| ≤ δ := by
    intro a b
    fin_cases a <;> simp only [P, R, rows, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two] <;> apply hdiff
  have herr := det_sub_bound (by positivity : 0 ≤ 2 * A) hδ hPr hRr hPR
  have hscaled : 2 * A * |P.det - R.det| ≤ 1 := by
    calc
      _ ≤ 2 * A * (18 * (2 * A) ^ 2 * δ) := by gcongr
      _ = 144 * A ^ 774 * ε := by dsimp [δ]; ring
      _ ≤ A ^ (774 + 8) * ε :=
        mul_le_mul_of_nonneg_right (absorb_constant hA (by norm_num)) hε
      _ ≤ A ^ 10000 * ε :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA1 (by norm_num : 774 + 8 ≤ 10000)) hε
      _ = ε * A ^ 10000 := by ring
      _ ≤ 1 := hs
  have htri : |R.det| ≤ |P.det| + |P.det - R.det| := by
    calc
      _ = |P.det - (P.det - R.det)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  have htri' := mul_le_mul_of_nonneg_left htri (by positivity : 0 ≤ 2 * A)
  have hfloor : 1 ≤ A * |R.det| := hdet i j k hij hik hjk
  apply (inv_le_iff_one_le_mul₀ (by positivity : 0 < 2 * A)).mpr
  change 1 ≤ |P.det| * (2 * A)
  nlinarith

end Submission.Obl.k4_real_conic_restoration
