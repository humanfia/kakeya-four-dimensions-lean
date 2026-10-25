import Submission.Obl.k4_physical_parent_potential_candidates.PointwiseConic

namespace Submission.Obl.k4_physical_parent_potential_candidates

open MvPolynomial
open scoped BigOperators
open Submission.Obl.k4_approximate_conic_taylor_decomposition
open Submission.Obl.k4_real_conic_restoration (quad coeff coeff_nonneg entry_le_coeff)

noncomputable section

set_option maxRecDepth 4000

namespace PointwiseConic

/-- Seven-direction norming with independent Hessian and cubic sizes and
independent test errors. This permits the Hessian of an implicit graph to be
paired with the much smaller cubic tensor of its defining potential. -/
theorem mixed_cleared_bound :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ (A MH MF ηq ηc : ℝ),
      2 ≤ A → 0 ≤ MH → 0 ≤ MF → 0 ≤ ηq → 0 ≤ ηc →
      ∀ (p : Fin 7 → E3) (H : Matrix (Fin 3) (Fin 3) ℝ)
        (F : MvPolynomial (Fin 3) ℝ),
      (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) →
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) →
      H.IsSymm → (∀ i j, |H i j| ≤ MH) → F.IsHomogeneous 3 →
      (∀ m, |F.coeff m| ≤ MF) →
      (∀ i, |quad H (fun j => p i j)| ≤ ηq) →
      (∀ i, |eval (fun j => p i j) F| ≤ ηc) →
      ∀ i j k, |ConicTensor.cleared H (ConicTensor.third F) i j k| ≤
        A^J*(MH^3*ηc+MF*MH^2*ηq) := by
  obtain ⟨D, hD, hnorm⟩ := normalized_cleared_bound
  refine ⟨4*D+690, by omega, ?_⟩
  intro A MH MF ηq ηc hA hMH hMF hηq hηc p H F hp htr hH hentry hF hcoeff hquad htest
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  let m := coeff H
  have hm0 : 0 ≤ m := coeff_nonneg H
  have hmM : m ≤ 9*MH := Submission.Obl.k4_real_conic_restoration.coeff_le hentry
  have hHm (i j : Fin 3) : |H i j| ≤ m := entry_le_coeff H i j
  by_cases hmz : m = 0
  · have hz : H = 0 := by
      ext i j
      exact abs_eq_zero.mp (le_antisymm (by simpa [hmz] using hHm i j) (abs_nonneg _))
    intro i j k
    rw [hz]
    simp only [ConicTensor.cleared, fubiniCubic, Matrix.det_zero, zero_mul,
      Matrix.zero_apply, mul_zero, add_zero, sub_self, abs_zero]
    positivity
  have hm : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hmz)
  let Q : Matrix (Fin 3) (Fin 3) ℝ := m⁻¹ • H
  have hQ : Q.IsSymm := by
    change (m⁻¹ • H).transpose = m⁻¹ • H
    rw [Matrix.transpose_smul, hH]
  have hQnorm : coeff Q = 1 := by
    change (∑ i : Fin 3, ∑ j : Fin 3, |m⁻¹*H i j|) = 1
    simp only [abs_mul, abs_of_pos (inv_pos.mpr hm), ← Finset.mul_sum]
    change m⁻¹*m = 1
    exact inv_mul_cancel₀ hm.ne'
  have hHQ : H = m • Q := by
    ext i j
    dsimp only [Q, Matrix.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul]
  let δ := ηq/m
  have hδ : 0 ≤ δ := div_nonneg hηq hm.le
  have hQtest (i : Fin 7) : |quad Q (fun j => p i j)| ≤ A*δ := by
    have he : quad Q (fun j => p i j) = m⁻¹*quad H (fun j => p i j) := by
      dsimp only [quad, Q, Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.sum_univ_three]
      ring
    rw [he, abs_mul, abs_of_pos (inv_pos.mpr hm)]
    calc
      _ ≤ m⁻¹*ηq := mul_le_mul_of_nonneg_left (hquad i) (inv_nonneg.mpr hm.le)
      _ = δ := by dsimp [δ]; ring
      _ ≤ A*δ := le_mul_of_one_le_left hδ hA1
  have hm2 : m^2 ≤ 81*MH^2 := by
    convert pow_le_pow_left₀ hm.le hmM 2 using 1 <;> ring
  have hm3 : m^3 ≤ 729*MH^3 := by
    convert pow_le_pow_left₀ hm.le hmM 3 using 1 <;> ring
  have hm2MF : m^2*MF ≤ 81*MF*MH^2 := by
    convert mul_le_mul_of_nonneg_right hm2 hMF using 1 <;> ring
  by_cases hsmall : δ*A^(4*D+1) ≤ 1
  · have hbound := hnorm A MF δ ηc hA hMF hδ hηc p Q F hp htr hQ hQnorm hF hcoeff
      hQtest htest hsmall
    have hsum : m^3*ηc+MF*m^2*ηq ≤ 729*(MH^3*ηc+MF*MH^2*ηq) := by
      have h1 := mul_le_mul_of_nonneg_right hm3 hηc
      have h2 := mul_le_mul_of_nonneg_right hm2MF hηq
      nlinarith [mul_nonneg hMF (mul_nonneg (pow_nonneg hMH 2) hηq)]
    have h729 : (729:ℝ) ≤ A^10 :=
      (by norm_num : (729:ℝ) ≤ 2^10).trans (pow_le_pow_left₀ (by norm_num) hA 10)
    have hpower : A^(4*D+680)*729 ≤ A^(4*D+690) := by
      calc
        _ ≤ A^(4*D+680)*A^10 := mul_le_mul_of_nonneg_left h729 (by positivity)
        _ = _ := by rw [← pow_add]
    intro i j k
    calc
      _ = m^3*|ConicTensor.cleared Q (ConicTensor.third F) i j k| := by
        rw [hHQ, ConicTensor.cleared_smul, abs_mul, abs_of_nonneg (pow_nonneg hm.le 3)]
      _ ≤ m^3*(A^(4*D+680)*(ηc+MF*δ)) :=
        mul_le_mul_of_nonneg_left (hbound i j k) (pow_nonneg hm.le 3)
      _ = A^(4*D+680)*(m^3*ηc+MF*m^2*ηq) := by
        dsimp only [δ]
        field_simp
      _ ≤ A^(4*D+680)*(729*(MH^3*ηc+MF*MH^2*ηq)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_right hpower
          (by positivity : 0 ≤ MH^3*ηc+MF*MH^2*ηq) using 1 <;> ring
  · have hbig : m < ηq*A^(4*D+1) := by
      have hh : 1 < (ηq*A^(4*D+1))/m := by
        convert lt_of_not_ge hsmall using 1
        dsimp only [δ]
        ring
      simpa using (lt_div_iff₀ hm).mp hh
    have h6804 : (6804:ℝ) ≤ A^13 :=
      (by norm_num : (6804:ℝ) ≤ 2^13).trans (pow_le_pow_left₀ (by norm_num) hA 13)
    have hpower : 6804*A^(4*D+1) ≤ A^(4*D+690) := by
      calc
        _ ≤ A^13*A^(4*D+1) := mul_le_mul_of_nonneg_right h6804 (by positivity)
        _ = A^(4*D+14) := by rw [← pow_add]; congr 1; omega
        _ ≤ _ := pow_le_pow_right₀ hA1 (by omega)
    intro i j k
    calc
      _ ≤ 84*m^3*MF := ConicTensor.cleared_bound hm.le hMF hHm
        (fun i j k => ConicTensor.third_bound hF hMF hcoeff i j k) i j k
      _ = 84*(m^2*MF*m) := by ring
      _ ≤ 84*((81*MF*MH^2)*(ηq*A^(4*D+1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hm2MF hbig.le hm.le (by positivity)) (by norm_num)
      _ = (6804*A^(4*D+1))*(MF*MH^2*ηq) := by ring
      _ ≤ A^(4*D+690)*(MF*MH^2*ηq) :=
        mul_le_mul_of_nonneg_right hpower (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (mul_nonneg (pow_nonneg hMH 3) hηc)) (by positivity)

/-- The same mixed estimate for an actual symmetric trilinear derivative. -/
theorem mixed_multilinear_bound :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ (A MH MF ηq ηc : ℝ),
      2 ≤ A → 0 ≤ MH → 0 ≤ MF → 0 ≤ ηq → 0 ≤ ηc →
      ∀ (p : Fin 7 → E3) (H : Matrix (Fin 3) (Fin 3) ℝ) (T : E3 [×3]→L[ℝ] ℝ),
      (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) →
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) →
      H.IsSymm → (∀ i j, |H i j| ≤ MH) → IsSymmML T → ‖T‖ ≤ MF →
      (∀ i, |quad H (fun j => p i j)| ≤ ηq) →
      (∀ i, |T (fun _ => p i)| ≤ ηc) →
      ∀ i j k, |ConicTensor.cleared H (fun a b c => T ![e3 a,e3 b,e3 c]) i j k| ≤
        A^J*(MH^3*ηc+MF*MH^2*ηq) := by
  obtain ⟨J, hJ, hnorm⟩ := mixed_cleared_bound
  refine ⟨J+5, by omega, ?_⟩
  intro A MH MF ηq ηc hA hMH hMF hηq hηc p H T hp htr hH hentry hT hTnorm hquad htest
  have hA0 : 0 < A := by linarith
  have hcoeff (e : Fin 3 →₀ ℕ) : |(formPoly T).coeff e| ≤ 27*MF := by
    exact (coeff_formPoly_abs_le T e).trans (by norm_num; linarith)
  have htestF (i : Fin 7) : |eval (fun j => p i j) (formPoly T)| ≤ ηc := by
    simpa only [eval_formPoly] using htest i
  have hb := hnorm A MH (27*MF) ηq ηc hA hMH (by positivity) hηq hηc p H (formPoly T)
    hp htr hH hentry (formPoly_isHomogeneous T) hcoeff hquad htestF
  have hthird : ConicTensor.third (formPoly T) = fun a b c => T ![e3 a,e3 b,e3 c] := by
    funext a b c
    exact ConicTensor.third_formPoly T hT a b c
  rw [hthird] at hb
  have h27 : (27:ℝ) ≤ A^5 :=
    (by norm_num : (27:ℝ) ≤ 2^5).trans (pow_le_pow_left₀ (by norm_num) hA 5)
  intro i j k
  apply (hb i j k).trans
  calc
    _ ≤ A^J*(27*(MH^3*ηc+MF*MH^2*ηq)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hA0.le J)
      nlinarith [mul_nonneg (pow_nonneg hMH 3) hηc]
    _ ≤ A^(J+5)*(MH^3*ηc+MF*MH^2*ηq) := by
      have hh := mul_le_mul_of_nonneg_right h27
        (by positivity : 0 ≤ MH^3*ηc+MF*MH^2*ηq)
      convert mul_le_mul_of_nonneg_left hh (pow_nonneg hA0.le J) using 1 <;> ring

end PointwiseConic

end

end Submission.Obl.k4_physical_parent_potential_candidates
