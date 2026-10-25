import Submission.Obl.k4_physical_parent_potential_candidates.ConicTensor
import Submission.Obl.k4_approximate_conic_taylor_decomposition.RestoredDirections
import Submission.Obl.k4_approximate_conic_taylor_decomposition.CubicPerturbation

namespace Submission.Obl.k4_physical_parent_potential_candidates

open MvPolynomial
open scoped BigOperators
open Submission.Obl.k4_approximate_conic_taylor_decomposition
open Submission.Obl.k4_real_conic_restoration (quad coeff coeff_nonneg entry_le_coeff)

noncomputable section

set_option maxRecDepth 4000

namespace PointwiseConic

/-- Seven well separated directions control the cleared canonical tensor
for a coefficient-normalized Hessian. Quadratic and cubic errors are separate
so normalization never introduces a power loss in the accuracy. -/
theorem normalized_cleared_bound :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (A M δ ε : ℝ), 2 ≤ A → 0 ≤ M → 0 ≤ δ → 0 ≤ ε →
      ∀ (p : Fin 7 → E3) (H : Matrix (Fin 3) (Fin 3) ℝ)
        (F : MvPolynomial (Fin 3) ℝ),
      (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) →
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) →
      H.IsSymm → coeff H = 1 → F.IsHomogeneous 3 →
      (∀ m, |F.coeff m| ≤ M) →
      (∀ i, |quad H (fun j => p i j)| ≤ A*δ) →
      (∀ i, |eval (fun j => p i j) F| ≤ ε) → δ*A^(4*D+1) ≤ 1 →
      ∀ i j k, |ConicTensor.cleared H (ConicTensor.third F) i j k| ≤
        A^(4*D+680)*(ε+M*δ) := by
  obtain ⟨D, hD, hrestore⟩ := Backup.conditioned_conic_restoration
  refine ⟨D, hD, ?_⟩
  intro A M δ ε hA hM hδ hε p H F hp htr hH hnorm hF hcoeff hquad htest hsmall
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hAB : A ≤ A^6 := by simpa using pow_le_pow_right₀ hA1 (by decide : 1 ≤ 6)
  have hA4 : 1 ≤ A^4 := one_le_pow₀ hA1
  have hlo : (A^4)⁻¹ ≤ coeff H := by
    rw [hnorm]
    simpa using inv_le_one_of_one_le₀ hA4
  obtain ⟨hdet, p', hp', htr'⟩ := hrestore A δ hA hδ p H hp htr hH hlo
    (by simpa [hnorm] using hA4) hquad hsmall
  let a : Fin 7 → Fin 3 → ℝ := fun i j => p i j
  let b : Fin 7 → Fin 3 → ℝ := fun i j => p' i j
  let Δ := A^(4*D+1)*δ
  have hΔ : 0 ≤ Δ := by dsimp [Δ]; positivity
  have ha (i : Fin 7) (j : Fin 3) : |a i j| ≤ A^6 :=
    (abs_apply_le_norm (p i) j).trans ((hp i).2.trans hAB)
  have hb (i : Fin 7) (j : Fin 3) : |b i j| ≤ A^6 :=
    (abs_apply_le_norm (p' i) j).trans (hp' i).2.2.1
  have hab (i : Fin 7) (j : Fin 3) : |b i j-a i j| ≤ Δ :=
    (abs_apply_le_norm (p' i-p i) j).trans (hp' i).2.2.2
  have htrb (i j k : Fin 7) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      (A^6)⁻¹ ≤ |Matrix.det (Matrix.of ![b i,b j,b k])| := by
    convert htr' i j k hij hik hjk using 3
    ext r t
    fin_cases r <;> rfl
  have hqzero (i : Fin 7) : eval (b i) (Kit.matrixQuadratic H) = 0 := by
    rw [Kit.eval_matrixQuadratic]
    exact (hp' i).2.1
  have hqne : Kit.matrixQuadratic H ≠ 0 := Kit.matrixQuadratic_ne_zero H hH
    (abs_pos.mp ((inv_pos.mpr (pow_pos hA0 _)).trans_le hdet))
  obtain ⟨P, hP, herr⟩ := exists_cubic_approximation_near_conic a b (A^6) M Δ ε
    (hA.trans hAB) hM hΔ hε ha hb hab htrb (Kit.matrixQuadratic H)
    (Kit.matrixQuadratic_isHomogeneous H) hqne hqzero F hF hcoeff htest
  have hentry (i j : Fin 3) : |H i j| ≤ 1 := by simpa [hnorm] using entry_le_coeff H i j
  have hremhom : (F-Submission.Lib.K4CubicTests.matrixQuadratic H*P).IsHomogeneous 3 :=
    hF.sub ((Submission.Lib.K4CubicTests.matrixQuadratic_isHomogeneous H).mul hP)
  have hrem (i j k : Fin 3) :
      |ConicTensor.third (F-Submission.Lib.K4CubicTests.matrixQuadratic H*P) i j k| ≤
      (A^6)^109*(ε+81*(A^6)^2*M*Δ) :=
    ConicTensor.third_bound hremhom (by positivity) herr i j k
  have h84 : (84:ℝ) ≤ A^7 :=
    (by norm_num : (84:ℝ) ≤ 2^7).trans (pow_le_pow_left₀ (by norm_num) hA 7)
  have h6804 : (6804:ℝ) ≤ A^13 :=
    (by norm_num : (6804:ℝ) ≤ 2^13).trans (pow_le_pow_left₀ (by norm_num) hA 13)
  have hfirst : 84*A^654 ≤ A^(4*D+680) := by
    calc
      _ ≤ A^7*A^654 := mul_le_mul_of_nonneg_right h84 (by positivity)
      _ = A^661 := by ring
      _ ≤ _ := pow_le_pow_right₀ hA1 (by omega)
  have hsecond : 6804*A^(4*D+667) ≤ A^(4*D+680) := by
    calc
      _ ≤ A^13*A^(4*D+667) := mul_le_mul_of_nonneg_right h6804 (by positivity)
      _ = A^(4*D+680) := by rw [← pow_add]; congr 1; omega
  intro i j k
  rw [ConicTensor.cleared_eq_remainder H hH F P hP]
  calc
    _ ≤ 84*1^3*((A^6)^109*(ε+81*(A^6)^2*M*Δ)) :=
      ConicTensor.cleared_bound (by norm_num) (by positivity) hentry hrem i j k
    _ = (84*A^654)*ε+(6804*A^(4*D+667))*(M*δ) := by
      dsimp only [Δ]
      simp only [← pow_mul]
      rw [show 6*109 = 654 by decide, show 6*2 = 12 by decide]
      ring
    _ ≤ A^(4*D+680)*ε+A^(4*D+680)*(M*δ) :=
      add_le_add (mul_le_mul_of_nonneg_right hfirst hε)
        (mul_le_mul_of_nonneg_right hsecond (mul_nonneg hM hδ))
    _ = _ := by ring

/-- Pointwise seven-direction norming of the canonical cubic tensor with
the determinant denominator cleared. No Hessian lower bound and no smallness
assumption on the tests is needed. -/
theorem cleared_bound :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ (A M η : ℝ), 2 ≤ A → 1 ≤ M → 0 ≤ η →
      ∀ (p : Fin 7 → E3) (H : Matrix (Fin 3) (Fin 3) ℝ)
        (F : MvPolynomial (Fin 3) ℝ),
      (∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A) →
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|) →
      H.IsSymm → (∀ i j, |H i j| ≤ M) → F.IsHomogeneous 3 →
      (∀ m, |F.coeff m| ≤ M) →
      (∀ i, |quad H (fun j => p i j)| ≤ η) →
      (∀ i, |eval (fun j => p i j) F| ≤ η) →
      ∀ i j k, |ConicTensor.cleared H (ConicTensor.third F) i j k| ≤ A^J*M^3*η := by
  obtain ⟨D, hD, hnorm⟩ := normalized_cleared_bound
  refine ⟨4*D+690, by omega, ?_⟩
  intro A M η hA hM1 hη p H F hp htr hH hentry hF hcoeff hquad htest
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hM : 0 ≤ M := by linarith
  let m := coeff H
  have hm0 : 0 ≤ m := coeff_nonneg H
  have hmM : m ≤ 9*M := Submission.Obl.k4_real_conic_restoration.coeff_le hentry
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
  let δ := η/m
  have hδ : 0 ≤ δ := div_nonneg hη hm.le
  have hQtest (i : Fin 7) : |quad Q (fun j => p i j)| ≤ A*δ := by
    have he : quad Q (fun j => p i j) = m⁻¹*quad H (fun j => p i j) := by
      dsimp only [quad, Q, Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.sum_univ_three]
      ring
    rw [he, abs_mul, abs_of_pos (inv_pos.mpr hm)]
    calc
      _ ≤ m⁻¹*η := mul_le_mul_of_nonneg_left (hquad i) (inv_nonneg.mpr hm.le)
      _ = δ := by dsimp [δ]; ring
      _ ≤ A*δ := le_mul_of_one_le_left hδ hA1
  have hm2 : m^2 ≤ 81*M^2 := by
    convert pow_le_pow_left₀ hm.le hmM 2 using 1 <;> ring
  have hm3 : m^3 ≤ 729*M^3 := by
    convert pow_le_pow_left₀ hm.le hmM 3 using 1 <;> ring
  have hm2M : m^2*M ≤ 81*M^3 := by
    convert mul_le_mul_of_nonneg_right hm2 hM using 1 <;> ring
  by_cases hsmall : δ*A^(4*D+1) ≤ 1
  · have hbound := hnorm A M δ η hA hM hδ hη p Q F hp htr hQ hQnorm hF hcoeff
      hQtest htest hsmall
    have hsum : m^3+M*m^2 ≤ 810*M^3 := by nlinarith [hm2M]
    have h810 : (810:ℝ) ≤ A^10 :=
      (by norm_num : (810:ℝ) ≤ 2^10).trans (pow_le_pow_left₀ (by norm_num) hA 10)
    have hpower : A^(4*D+680)*810 ≤ A^(4*D+690) := by
      calc
        _ ≤ A^(4*D+680)*A^10 := mul_le_mul_of_nonneg_left h810 (by positivity)
        _ = _ := by rw [← pow_add]
    intro i j k
    calc
      _ = m^3*|ConicTensor.cleared Q (ConicTensor.third F) i j k| := by
        rw [hHQ, ConicTensor.cleared_smul, abs_mul, abs_of_nonneg (pow_nonneg hm.le 3)]
      _ ≤ m^3*(A^(4*D+680)*(η+M*δ)) :=
        mul_le_mul_of_nonneg_left (hbound i j k) (pow_nonneg hm.le 3)
      _ = A^(4*D+680)*(m^3+M*m^2)*η := by
        dsimp only [δ]
        field_simp
      _ ≤ A^(4*D+680)*(810*M^3)*η :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by positivity)) hη
      _ ≤ A^(4*D+690)*M^3*η := by
        convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpower
          (pow_nonneg hM 3)) hη using 1 <;> ring
  · have hbig : m < η*A^(4*D+1) := by
      have hh : 1 < (η*A^(4*D+1))/m := by
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
      _ ≤ 84*m^3*M := ConicTensor.cleared_bound hm.le hM hHm
        (fun i j k => ConicTensor.third_bound hF hM hcoeff i j k) i j k
      _ = 84*(m^2*M*m) := by ring
      _ ≤ 84*(81*M^3*(η*A^(4*D+1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hm2M hbig.le hm.le (by positivity)) (by norm_num)
      _ = (6804*A^(4*D+1))*M^3*η := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpower (pow_nonneg hM 3)) hη

end PointwiseConic

end

end Submission.Obl.k4_physical_parent_potential_candidates
