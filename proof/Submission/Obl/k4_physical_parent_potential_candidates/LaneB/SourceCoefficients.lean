import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourceNormalization
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.TransportBounds

namespace Submission.Obl.k4_physical_parent_potential_candidates

open MvPolynomial

noncomputable section

namespace SourceNormalization

/-- Original coordinate size and clock bounds control the actual forward
source frame after zoom by a fixed polynomial. -/
theorem forward_frame_bounds (T j : ℕ) (c u : P2) {K A H B lam : ℝ}
    (hK : 2 ≤ K) (hA : 2 ≤ A) (hH : 1 ≤ H) (hlam : 0 ≤ lam) (hlamA : lam ≤ A)
    (hclock : (2:ℝ)^T ≤ H) (hB : |B| ≤ H)
    (horigin : ∀ i, |Broad.parentBaseOrigin T j c u i| ≤ H)
    (cz : Fin 3 → ℝ) (hcz : ∀ i, |cz i| ≤ 1) :
    (∀ i, |Analytic.zoomForwardShift (shift T j c u (8*K) (fun _ => 1/8)) cz lam i| ≤ A^3*H^2) ∧
    (∀ i k, |(lam • matrix T (8*K)) i k| ≤ A^3*H^2) ∧
    |B| ≤ A^3*H^2 := by
  have hK0 : 0 < K := by linarith
  have hA0 : 0 < A := by linarith
  have hH0 : 0 < H := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hH2 : H ≤ H^2 := by nlinarith only [hH]
  have hH21 : 1 ≤ H^2 := one_le_pow₀ hH
  have hA3 : 3*A ≤ A^3 := by
    have hAA : 4 ≤ A^2 := by nlinarith only [hA]
    nlinarith only [hAA,hA0]
  have hinv : 0 < (scale T (8*K))⁻¹ := by
    exact inv_pos.mpr (scale_pos T (by positivity))
  have hinvH : (scale T (8*K))⁻¹ ≤ H := by
    have heq : (scale T (8*K))⁻¹ = (2:ℝ)^T/(8*K) := by dsimp only [scale]; field_simp
    rw [heq]
    exact (div_le_self (by positivity) (by linarith : 1 ≤ 8*K)).trans hclock
  have hFH : H ≤ A^3*H^2 :=
    hH2.trans (le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hA1))
  refine ⟨?_,?_,hB.trans hFH⟩
  · intro i
    simp only [Analytic.zoomForwardShift,abs_mul,abs_of_nonneg hlam]
    have hshift : |shift T j c u (8*K) (fun _ => 1/8) i| ≤ 1+H^2 := by
      dsimp only [shift]
      calc
        _ ≤ |(1:ℝ)/8|+|(scale T (8*K))⁻¹*Broad.parentBaseOrigin T j c u i| := abs_sub _ _
        _ ≤ 1+H*H := by
          apply add_le_add (by norm_num)
          rw [abs_mul,abs_of_pos hinv]
          exact mul_le_mul hinvH (horigin i) (abs_nonneg _) hH0.le
        _ = _ := by ring
    calc
      _ ≤ A*((1+H^2)+1) := mul_le_mul hlamA
        ((abs_sub _ _).trans (add_le_add hshift (hcz i))) (abs_nonneg _) hA0.le
      _ ≤ A*(3*H^2) := by gcongr; linarith only [hH21]
      _ ≤ A^3*H^2 := by nlinarith only [mul_le_mul_of_nonneg_right hA3 (sq_nonneg H)]
  · intro i k
    simp only [matrix,Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg hlam,
      abs_of_pos hinv]
    have hone : |(1:Matrix (Fin 3) (Fin 3) ℝ) i k| ≤ 1 := by
      by_cases hik : i=k <;> simp [Matrix.one_apply,hik]
    calc
      _ ≤ A*(H*1) := by gcongr
      _ ≤ A^3*H^2 := by
        have hp : A ≤ A^3 := by simpa using pow_le_pow_right₀ hA1 (by decide : 1 ≤ 3)
        simpa only [mul_one] using mul_le_mul hp hH2 hH0.le (by positivity)

def coefficientPower (M C : ℕ) : ℕ := M*(C+40)+20

/-- The normalized coefficient format, including inverse target thickness,
returns to the format allowed by the packet with a fixed exponent. -/
theorem restored_source_coefficients {K H a w Eb Vf : ℝ} (M C : ℕ)
    (hK : 2 ≤ K) (hM : 1 ≤ M) (hH : 1 ≤ H) (haw : 0 < a*w)
    (hwidth : a*w ≤ Eb) (hVf0 : 0 ≤ Vf) (hVf : Vf ≤ 4*H)
    (cf : Fin 3 → ℝ) (Mf : Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ) (Q : Po)
    (hcf : ∀ i, |cf i| ≤ (K^M)^3*H^2)
    (hMf : ∀ i k, |Mf i k| ≤ (K^M)^3*H^2)
    (hB : |B| ≤ (K^M)^3*H^2)
    (hQ : Q.totalDegree ≤ 2)
    (hcoeff : ∀ m, |Q.coeff m| ≤ (K^M)^C*(1+Vf+Eb⁻¹)^5) :
    ∀ m, |(Analytic.transportPolynomial cf Mf B Q).coeff m| ≤
      (K*H*(1+(a*w)⁻¹))^coefficientPower M C := by
  let A : ℝ := K^M
  let X : ℝ := 1+(a*w)⁻¹
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hA : 2 ≤ A := hK.trans (by simpa only [A,pow_one] using pow_le_pow_right₀ hK1 hM)
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hH0 : 0 < H := by linarith
  have hX : 1 ≤ X := by
    dsimp only [X]
    exact le_add_of_nonneg_right (inv_nonneg.mpr haw.le)
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hEb0 : 0 < Eb := haw.trans_le hwidth
  have hinv := inv_anti₀ haw hwidth
  have hsum : 1+Vf+Eb⁻¹ ≤ 6*H*X := by
    have hXi : 0 ≤ (a*w)⁻¹ := inv_nonneg.mpr haw.le
    dsimp only [X]
    nlinarith only [hVf,hinv,hH,hXi,mul_nonneg (sub_nonneg.mpr hH) hXi]
  have h6 : (6:ℝ) ≤ A^3 :=
    (by norm_num : (6:ℝ) ≤ 2^3).trans (pow_le_pow_left₀ (by norm_num) hA 3)
  have hsumA : 1+Vf+Eb⁻¹ ≤ A^3*H*X :=
    hsum.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h6 hH0.le) hX0)
  have hZ : ∀ m, |Q.coeff m| ≤ A^(C+15)*H^5*X^5 := by
    intro m
    calc
      _ ≤ A^C*(1+Vf+Eb⁻¹)^5 := hcoeff m
      _ ≤ A^C*(A^3*H*X)^5 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hsumA 5) (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hframe : 1 ≤ A^3*H^2 := by
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hA1) (one_le_pow₀ hH)
  have h1296 : (1296:ℝ) ≤ A^11 :=
    (by norm_num : (1296:ℝ) ≤ 2^11).trans (pow_le_pow_left₀ (by norm_num) hA 11)
  have hpower : M*(C+32) ≤ coefficientPower M C := by
    dsimp only [coefficientPower]
    exact (Nat.mul_le_mul_left M (by omega : C+32 ≤ C+40)).trans (by omega)
  intro m
  calc
    _ ≤ 1296*(A^(C+15)*H^5*X^5)*(A^3*H^2)^2 :=
      Analytic.transportPolynomial_coeff_bound cf Mf B Q hframe (by positivity)
        hcf hMf hB hQ hZ m
    _ ≤ A^11*(A^(C+15)*H^5*X^5)*(A^3*H^2)^2 := by gcongr
    _ = K^(M*(C+32))*H^9*X^5 := by dsimp only [A]; simp only [pow_add,pow_mul]; ring
    _ ≤ K^coefficientPower M C*H^coefficientPower M C*X^coefficientPower M C := by
      apply mul_le_mul
      · exact mul_le_mul (pow_le_pow_right₀ hK1 hpower)
          (pow_le_pow_right₀ hH (by dsimp only [coefficientPower]; omega))
          (by positivity) (by positivity)
      · exact pow_le_pow_right₀ hX (by dsimp only [coefficientPower]; omega)
      · positivity
      · positivity
    _ = _ := by dsimp only [X]; rw [mul_pow,mul_pow]

end SourceNormalization

end

end Submission.Obl.k4_physical_parent_potential_candidates
