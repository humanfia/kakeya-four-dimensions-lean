import Submission.Obl.k4_real_conic_restoration.NormalForm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Submission.Obl.k4_real_conic_restoration

theorem absorb_constant {A c : ℝ} {m k : ℕ} (hA : 2 ≤ A) (hc : c ≤ (2 : ℝ) ^ k) :
    c * A ^ m ≤ A ^ (m + k) := by
  have hA0 : 0 ≤ A := by linarith
  calc
    _ ≤ A ^ k * A ^ m := by
      gcongr
      exact hc.trans (pow_le_pow_left₀ (by norm_num) hA k)
    _ = _ := by rw [pow_add]; ring

theorem inverse_entry_bound {P : Mat} {A : ℝ} (hA : 0 < A)
    (hP : ∀ i j, |P i j| ≤ A) (hd : 1 ≤ A * |P.det|) :
    ∀ i j, |P⁻¹ i j| ≤ 2 * A ^ 3 := by
  have hd0 : 0 < |P.det| := by nlinarith [abs_nonneg P.det]
  have hi : |P.det|⁻¹ ≤ A := (inv_le_iff_one_le_mul₀ hd0).mpr hd
  intro i j
  rw [Matrix.inv_def]
  simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv, abs_mul, abs_inv]
  calc
    _ ≤ A * (2 * A ^ 2) := mul_le_mul hi (adjugate_bound hP i j) (abs_nonneg _) (le_of_lt hA)
    _ = _ := by ring

/-- Determinant conditioning, transferred to projective coordinates. Only five points are used. -/
theorem conditioned_det {p : Fin 7 → Vec} {Q : Mat} {A ε : ℝ}
    (hA : 2 ≤ A) (hp : ∀ i j, |p i j| ≤ A)
    (hdet : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      1 ≤ A * |(rows (p i) (p j) (p k)).det|)
    (hQ : Q.IsSymm) (hQl : 1 ≤ A * coeff Q) (hQu : ∀ i j, |Q i j| ≤ A)
    (hε : 0 ≤ ε) (hs : ε * A ^ 1000 ≤ 1) (hq : ∀ i, |quad Q (p i)| ≤ ε) :
    1 ≤ A ^ 760 * |Q.det| := by
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  let P : Mat := rows (p 0) (p 1) (p 2)
  let S : Mat := P * Q * P.transpose
  let r : Fin 7 → Vec := fun i => Matrix.vecMul (p i) P⁻¹
  let B : ℝ := A ^ 20
  have hP : ∀ i j, |P i j| ≤ A := by
    intro i j
    fin_cases i <;> simp only [P, rows, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two] <;> apply hp
  have hPl : 1 ≤ A * |P.det| := hdet 0 1 2 (by decide) (by decide) (by decide)
  have hPd : P.det ≠ 0 := by
    intro he
    simp only [he, abs_zero, mul_zero] at hPl
    norm_num at hPl
  have huP : IsUnit P.det := isUnit_iff_ne_zero.mpr hPd
  have hiP := inverse_entry_bound hA0 hP hPl
  have hB4 : 4 ≤ B := by
    dsimp [B]
    exact (show (4 : ℝ) ≤ 2 ^ 20 by norm_num).trans (pow_le_pow_left₀ (by norm_num) hA 20)
  have hBu : A * |P.det| ≤ B := by
    calc
      _ ≤ A * (6 * A ^ 3) := by gcongr; exact det_bound hP
      _ = 6 * A ^ 4 := by ring
      _ ≤ A ^ (4 + 16) := absorb_constant hA (by norm_num)
  have hSb : ∀ i j, |S i j| ≤ B := by
    have h := mul_entry_bound (mul_entry_bound hP hQu) (fun i j => hP j i)
    intro i j
    calc
      |S i j| ≤ 3 * (3 * A * A) * A := h i j
      _ = 9 * A ^ 3 := by ring
      _ ≤ A ^ (3 + 17) := absorb_constant hA (by norm_num)
  have hcb : coeff Q ≤ 324 * A ^ 6 * coeff S := by
    have hrecover : P⁻¹ * S * P⁻¹.transpose = Q := by
      dsimp [S]
      calc
        _ = (P⁻¹ * P) * Q * (P.transpose * P⁻¹.transpose) := by noncomm_ring
        _ = Q := by rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul P huP]; simp
    have hb := mul_entry_bound
      (mul_entry_bound hiP (fun i j => entry_le_coeff S i j)) (fun i j => hiP j i)
    have hh := coeff_le (Q := Q) (B := 3 * (3 * (2 * A ^ 3) * coeff S) * (2 * A ^ 3))
      (by intro i j; rw [← hrecover]; exact hb i j)
    exact hh.trans_eq (by ring)
  have hSc : 1 ≤ B * coeff S := by
    calc
      1 ≤ A * coeff Q := hQl
      _ ≤ A * (324 * A ^ 6 * coeff S) := by gcongr
      _ = (324 * A ^ 7) * coeff S := by ring
      _ ≤ A ^ (7 + 13) * coeff S := by
        exact mul_le_mul_of_nonneg_right (absorb_constant hA (by norm_num)) (coeff_nonneg S)
  have hrb : ∀ i j, |r i j| ≤ B := by
    intro i j
    calc
      |r i j| ≤ 3 * A * (2 * A ^ 3) := vecMul_bound (hp i) hiP j
      _ = 6 * A ^ 4 := by ring
      _ ≤ A ^ (4 + 16) := absorb_constant hA (by norm_num)
  have hback (i : Fin 7) : Matrix.vecMul (r i) P = p i := by
    dsimp [r]
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul P huP, Matrix.vecMul_one]
  have hr0 : r 0 = ![1, 0, 0] := by
    change Matrix.vecMul (P 0) P⁻¹ = _
    have hh : Matrix.vecMul (P 0) P⁻¹ = (1 : Mat) 0 :=
      congrArg (fun M : Mat => M 0) (Matrix.mul_nonsing_inv P huP)
    rw [hh]
    ext j
    fin_cases j <;> simp [Matrix.one_apply]
  have hr1 : r 1 = ![0, 1, 0] := by
    change Matrix.vecMul (P 1) P⁻¹ = _
    have hh : Matrix.vecMul (P 1) P⁻¹ = (1 : Mat) 1 :=
      congrArg (fun M : Mat => M 1) (Matrix.mul_nonsing_inv P huP)
    rw [hh]
    ext j
    fin_cases j <;> simp [Matrix.one_apply]
  have hr2 : r 2 = ![0, 0, 1] := by
    change Matrix.vecMul (P 2) P⁻¹ = _
    have hh : Matrix.vecMul (P 2) P⁻¹ = (1 : Mat) 2 :=
      congrArg (fun M : Mat => M 2) (Matrix.mul_nonsing_inv P huP)
    rw [hh]
    ext j
    fin_cases j <;> simp [Matrix.one_apply]
  have hrc (i j k : Fin 7) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      1 ≤ B * |(rows (r i) (r j) (r k)).det| := by
    have heq := det_rows_mul (r i) (r j) (r k) P
    rw [hback, hback, hback] at heq
    calc
      1 ≤ A * |(rows (p i) (p j) (p k)).det| := hdet i j k hij hik hjk
      _ = (A * |P.det|) * |(rows (r i) (r j) (r k)).det| := by rw [heq, abs_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hBu (abs_nonneg _)
  have hrl (i : Fin 7) (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
      ∀ j, 1 ≤ B * |r i j| := by
    have h0 := hrc 1 2 i (by decide) hi1.symm hi2.symm
    have h1 := hrc 0 2 i (by decide) hi0.symm hi2.symm
    have h2 := hrc 0 1 i (by decide) hi0.symm hi1.symm
    intro j
    fin_cases j
    · simpa [rows, Matrix.det_fin_three, hr1, hr2] using h0
    · simpa [rows, Matrix.det_fin_three, hr0, hr2] using h1
    · simpa [rows, Matrix.det_fin_three, hr0, hr1] using h2
  have hrm : ∀ i j, i ≠ j → 1 ≤ B * |r 3 i * r 4 j - r 4 i * r 3 j| := by
    have h0 := hrc 0 3 4 (by decide) (by decide) (by decide)
    have h1 := hrc 1 3 4 (by decide) (by decide) (by decide)
    have h2 := hrc 2 3 4 (by decide) (by decide) (by decide)
    simp [rows, Matrix.det_fin_three, hr0, hr1, hr2] at h0 h1 h2
    have h01 : 1 ≤ B * |r 3 0 * r 4 1 - r 4 0 * r 3 1| := by
      convert h2 using 1
      congr 2
      ring
    have h02 : 1 ≤ B * |r 3 0 * r 4 2 - r 4 0 * r 3 2| := by
      convert h1 using 1
      rw [← abs_neg (r 3 0 * r 4 2 - r 4 0 * r 3 2)]
      congr 2
      ring
    have h12 : 1 ≤ B * |r 3 1 * r 4 2 - r 4 1 * r 3 2| := by
      convert h0 using 1
      congr 2
      ring
    have hswap (i j : Fin 3) : |r 3 i * r 4 j - r 4 i * r 3 j| =
        |r 3 j * r 4 i - r 4 j * r 3 i| := by
      rw [← abs_neg (r 3 j * r 4 i - r 4 j * r 3 i)]
      congr 1
      ring
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact h01
    · exact h02
    · rw [hswap]; exact h01
    · exact (hij rfl).elim
    · exact h12
    · rw [hswap]; exact h02
    · rw [hswap]; exact h12
    · exact (hij rfl).elim
  have hSq : ∀ i, |quad S (r i)| ≤ ε := by
    intro i
    change |quad (P * Q * P.transpose) (r i)| ≤ ε
    rw [quad_vecMul, hback]
    exact hq i
  have hSd : ∀ i, |S i i| ≤ ε := by
    intro i
    change |(P * Q * P.transpose) i i| ≤ ε
    rw [quad_row]
    fin_cases i <;> simp only [P, rows, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two] <;> apply hq
  have hn := normal_form_det_lower hB4 hε (by simpa [B, ← pow_mul] using hs)
    (symm_congr hQ P) hSd hSc hSb (hrb 3) (hrb 4)
    (hrl 3 (by decide) (by decide) (by decide))
    (hrl 4 (by decide) (by decide) (by decide)) hrm (hSq 3) (hSq 4)
  have hPdB : |P.det| ≤ B := by
    calc
      _ ≤ 6 * A ^ 3 := det_bound hP
      _ ≤ A ^ (3 + 17) := absorb_constant hA (by norm_num)
  have hSdQ : |S.det| = |P.det| ^ 2 * |Q.det| := by
    simp only [S, Matrix.det_mul, Matrix.det_transpose, abs_mul]
    ring
  calc
    1 ≤ B ^ 36 * |S.det| := hn
    _ ≤ B ^ 36 * (B ^ 2 * |Q.det|) := by rw [hSdQ]; gcongr
    _ = A ^ 760 * |Q.det| := by dsimp [B]; ring

end Submission.Obl.k4_real_conic_restoration
