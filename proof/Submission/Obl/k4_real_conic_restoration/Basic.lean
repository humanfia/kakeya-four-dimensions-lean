import Mathlib
import ChallengeDeps

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Submission.Obl.k4_real_conic_restoration

abbrev Vec := Fin 3 → ℝ
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

def quad (Q : Mat) (v : Vec) : ℝ := ∑ a, ∑ b, v a * Q a b * v b

def coeff (Q : Mat) : ℝ := ∑ a, ∑ b, |Q a b|

def rows (u v w : Vec) : Mat := Matrix.of ![u, v, w]

theorem abs_sum_le {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _

theorem abs_sum3 {f : Fin 3 → ℝ} {B : ℝ} (h : ∀ i, |f i| ≤ B) :
    |∑ i, f i| ≤ 3 * B := by
  calc
    _ ≤ ∑ i, |f i| := abs_sum_le _
    _ ≤ ∑ _ : Fin 3, B := Finset.sum_le_sum fun i _ => h i
    _ = _ := by simp

theorem sum3_le {f : Fin 3 → ℝ} {B : ℝ} (h : ∀ i, f i ≤ B) :
    ∑ i, f i ≤ 3 * B := by
  calc
    _ ≤ ∑ _ : Fin 3, B := Finset.sum_le_sum fun i _ => h i
    _ = _ := by simp

theorem coeff_nonneg (Q : Mat) : 0 ≤ coeff Q :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem entry_le_coeff (Q : Mat) (i j : Fin 3) : |Q i j| ≤ coeff Q := by
  exact (Finset.single_le_sum (fun b _ => abs_nonneg (Q i b)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => abs_nonneg (Q a b))
      (Finset.mem_univ i))

theorem coeff_le {Q : Mat} {B : ℝ} (h : ∀ i j, |Q i j| ≤ B) : coeff Q ≤ 9 * B := by
  exact (sum3_le fun i => sum3_le (h i)).trans_eq (by ring)

theorem mul_entry_bound {Q R : Mat} {B C : ℝ}
    (hQ : ∀ i j, |Q i j| ≤ B) (hR : ∀ i j, |R i j| ≤ C) :
    ∀ i j, |(Q * R) i j| ≤ 3 * B * C := by
  intro i j
  simpa only [Matrix.mul_apply, mul_assoc] using
    (abs_sum3 (fun k => by
      rw [abs_mul]
      exact mul_le_mul (hQ i k) (hR k j) (abs_nonneg _) ((abs_nonneg _).trans (hQ i k))))

theorem vecMul_bound {v : Vec} {Q : Mat} {B C : ℝ}
    (hv : ∀ i, |v i| ≤ B) (hQ : ∀ i j, |Q i j| ≤ C) :
    ∀ j, |Matrix.vecMul v Q j| ≤ 3 * B * C := by
  intro j
  simpa only [Matrix.vecMul, dotProduct, mul_assoc] using
    (abs_sum3 (fun k => by
      rw [abs_mul]
      exact mul_le_mul (hv k) (hQ k j) (abs_nonneg _) ((abs_nonneg _).trans (hv k))))

theorem quad_bound {Q : Mat} {v : Vec} {B C : ℝ}
    (hQ : ∀ i j, |Q i j| ≤ B) (hv : ∀ i, |v i| ≤ C) :
    |quad Q v| ≤ 9 * C * B * C := by
  unfold quad
  calc
    _ ≤ 3 * (3 * (C * B * C)) := abs_sum3 fun a => abs_sum3 fun b => by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (hv a) (hQ a b) (abs_nonneg _)
        ((abs_nonneg _).trans (hv a))) (hv b) (abs_nonneg _)
        (mul_nonneg ((abs_nonneg _).trans (hv a)) ((abs_nonneg _).trans (hQ a b)))
    _ = _ := by ring

theorem quad_vecMul (Q P : Mat) (v : Vec) :
    quad (P * Q * P.transpose) v = quad Q (Matrix.vecMul v P) := by
  simp only [quad, Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMul, dotProduct,
    Fin.sum_univ_three]
  ring

theorem quad_row (Q P : Mat) (i : Fin 3) :
    (P * Q * P.transpose) i i = quad Q (P i) := by
  simp only [quad, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  ring

theorem symm_congr {Q : Mat} (hQ : Q.IsSymm) (P : Mat) :
    (P * Q * P.transpose).IsSymm := by
  change (P * Q * P.transpose).transpose = _
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hQ.eq, Matrix.mul_assoc]

theorem det_rows_mul (u v w : Vec) (P : Mat) :
    (rows (Matrix.vecMul u P) (Matrix.vecMul v P) (Matrix.vecMul w P)).det =
      (rows u v w).det * P.det := by
  rw [← Matrix.det_mul]
  congr 1
  ext i j
  fin_cases i <;> simp [rows, Matrix.mul_apply, Matrix.vecMul, dotProduct]

theorem det_bound {Q : Mat} {B : ℝ} (h : ∀ i j, |Q i j| ≤ B) :
    |Q.det| ≤ 6 * B ^ 3 := by
  have hb : 0 ≤ B := (abs_nonneg _).trans (h 0 0)
  have ht (i j k l m n : Fin 3) : |Q i j * Q k l * Q m n| ≤ B ^ 3 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ B * B * B := mul_le_mul (mul_le_mul (h i j) (h k l) (abs_nonneg _) hb)
        (h m n) (abs_nonneg _) (mul_nonneg hb hb)
      _ = _ := by ring
  have h1 := abs_le.mp (ht 0 0 1 1 2 2)
  have h2 := abs_le.mp (ht 0 0 1 2 2 1)
  have h3 := abs_le.mp (ht 0 1 1 0 2 2)
  have h4 := abs_le.mp (ht 0 1 1 2 2 0)
  have h5 := abs_le.mp (ht 0 2 1 0 2 1)
  have h6 := abs_le.mp (ht 0 2 1 1 2 0)
  rw [Matrix.det_fin_three]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem adjugate_bound {Q : Mat} {B : ℝ} (h : ∀ i j, |Q i j| ≤ B) :
    ∀ i j, |Q.adjugate i j| ≤ 2 * B ^ 2 := by
  have hb : 0 ≤ B := (abs_nonneg _).trans (h 0 0)
  have ht (i j k l : Fin 3) : |Q i j * Q k l| ≤ B ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (h i j) (h k l) (abs_nonneg _) hb
  have hd (i j k l m n o p : Fin 3) :
      |Q i j * Q k l - Q m n * Q o p| ≤ 2 * B ^ 2 := by
    exact (abs_sub _ _).trans (by linarith [ht i j k l, ht m n o p])
  have hn (i j k l m n o p : Fin 3) :
      |-(Q i j * Q k l) + Q m n * Q o p| ≤ 2 * B ^ 2 := by
    simpa only [sub_eq_add_neg, add_comm] using hd m n o p i j k l
  intro i j
  rw [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;> first | apply hd | apply hn

end Submission.Obl.k4_real_conic_restoration
