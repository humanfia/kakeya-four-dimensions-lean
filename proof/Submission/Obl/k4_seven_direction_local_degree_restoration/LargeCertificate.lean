import Submission.Obl.k4_seven_direction_local_degree_restoration.CorrectionPoly
import Submission.Obl.k4_seven_direction_local_degree_restoration.CorrectionNumerics

namespace Submission.Obl.k4_seven_direction_local_degree_restoration

open MvPolynomial

/-- Converts a conic Taylor decomposition into the complete local quadratic certificate. -/
theorem large_case_of_decomposition (K C : ℕ) (hK : 6 ≤ K) (hC : 3 * K + 20 ≤ C)
    {A Z a b h s : ℝ} {S : Poly} {f R q : Base → ℝ} {L : Base →L[ℝ] ℝ} {lam : ℝ}
    (hA : 2 ≤ A) (hAZ : A ≤ Z) (hb : 0 < b) (hba : b ≤ a) (ha1 : a ≤ 1)
    (hh : 0 < h) (hscale : h * A ^ C ≤ b / a) (hlarge : b < s * h) (hbinv : b⁻¹ ≤ Z)
    (hSdeg : S.totalDegree ≤ 2) (hScoeff : ∀ e, |S.coeff e| ≤ Z)
    (hScurv : ∀ u w, |evalAt (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) S)) u w| ≤ A / a)
    (hf0 : |f 0| ≤ Z) (hf1 : ‖fderiv ℝ f 0‖ ≤ Z)
    (hR : ∀ u, a * R u = evalAt S u (f u))
    (hR0 : |R 0| ≤ A) (hR1 : ‖fderiv ℝ R 0‖ ≤ A) (hR2 : ‖iteratedFDeriv ℝ 2 R 0‖ ≤ A)
    (hq : ∀ u ∈ Metric.closedBall (0 : Base) 1, |q u| ≤ A ^ K)
    (hfq : ∀ u ∈ Metric.closedBall (0 : Base) 1,
      |(f u - f 0 - fderiv ℝ f 0 u) / s - q u| ≤ A ^ K * h)
    (hL : ‖L‖ ≤ A ^ K) (hlam : |lam| ≤ A ^ K)
    (happrox : ∀ u ∈ Metric.closedBall (0 : Base) 1,
      |R u - (R 0 + fderiv ℝ R 0 u + iteratedFDeriv ℝ 2 R 0 (fun _ => u) / 2 +
        q u * L u + lam * (q u) ^ 2)| ≤ A ^ K * b / a) :
    ∃ Q : Poly, Q.totalDegree ≤ 2 ∧ (∀ e, |Q.coeff e| ≤ Z ^ C) ∧
      ∀ u ∈ Metric.closedBall (0 : Base) 1, ∀ w : ℝ, |w - f u| ≤ A * b →
      A⁻¹ ≤ |evalAt (pderiv (3 : Fin 4) S) u w| →
      |evalAt (pderiv (3 : Fin 4) S) u w| ≤ A →
      |evalAt Q u w| ≤ A ^ C * b ∧ A ^ (-(C : ℤ)) ≤ |evalAt (pderiv (3 : Fin 4) Q) u w| ∧
      |evalAt (pderiv (3 : Fin 4) Q) u w| ≤ A ^ C ∧
      |evalAt (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q)) u w| ≤ A ^ C / b := by
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hZ : 2 ≤ Z := hA.trans hAZ
  have hZ1 : 1 ≤ Z := by linarith
  have ha : 0 < a := hb.trans_le hba
  have hpow : 1 ≤ A ^ C := one_le_pow₀ hA1
  have hhratio : h ≤ b / a := by
    have ht : h ≤ h * A ^ C := by simpa using mul_le_mul_of_nonneg_left hpow hh.le
    exact ht.trans hscale
  have hah : a * h ≤ b := by
    have ht := (le_div_iff₀ ha).1 hhratio
    nlinarith only [ht]
  have has : a ≤ s := le_of_mul_le_mul_right (hah.trans hlarge.le) hh
  have hs : 0 < s := ha.trans_le has
  have hsinv : s⁻¹ ≤ Z := by
    have ht := one_div_le_one_div_of_le hb (hba.trans has)
    have ht' : s⁻¹ ≤ b⁻¹ := by simpa only [one_div] using ht
    exact ht'.trans hbinv
  have hh1 : h ≤ 1 := hhratio.trans ((div_le_one₀ ha).2 hba)
  have hAM : A ≤ A ^ K := by
    simpa using pow_le_pow_right₀ hA1 (by omega : 1 ≤ K)
  have hM : 1 ≤ A ^ K := one_le_pow₀ hA1
  have hM0 : 0 ≤ A ^ K := pow_nonneg hA0.le K
  have hAKZ : A ^ K ≤ Z ^ K := pow_le_pow_left₀ hA0.le hAZ K
  refine ⟨correctedPolynomial S f R a s L lam,
    correctedPolynomial_totalDegree _ _ _ _ _ _ _ hSdeg, ?_, ?_⟩
  · intro e
    exact (correctedPolynomial_coeff_bound K (by omega) hZ ha.le ha1 hs hsinv hScoeff hf0 hf1
      (hR0.trans hAZ) (hR1.trans hAZ) (hR2.trans hAZ) (hL.trans hAKZ) (hlam.trans hAKZ) e).trans
      (pow_le_pow_right₀ hZ1 (by omega : K + 10 ≤ C))
  · intro u hu w hw hlow hupp
    let H := evalAt (hiddenAffine f s) u w
    have hu' : ‖u‖ ≤ 1 := by simpa using hu
    have hLu : |L u| ≤ A ^ K := by
      have ht : |L u| ≤ ‖L‖ * ‖u‖ := by simpa only [Real.norm_eq_abs] using L.le_opNorm u
      exact ht.trans ((mul_le_mul hL hu' (norm_nonneg u) hM0).trans_eq (mul_one _))
    have hbs : b / s ≤ h := (div_le_iff₀ hs).2 (by nlinarith only [hlarge])
    have hclose : |H - q u| ≤ 2 * A ^ K * h := by
      have he : H - q u = (w - f u) / s + ((f u - f 0 - fderiv ℝ f 0 u) / s - q u) := by
        dsimp [H]
        rw [hiddenAffine_eval]
        ring
      rw [he]
      refine (abs_add_le _ _).trans ?_
      rw [abs_div, abs_of_pos hs]
      have ht : |w - f u| / s ≤ A * h := by
        calc |w - f u| / s ≤ (A * b) / s := div_le_div_of_nonneg_right hw hs.le
             _ = A * (b / s) := by ring
             _ ≤ A * h := mul_le_mul_of_nonneg_left hbs hA0.le
      have ht' := mul_le_mul_of_nonneg_right hAM hh.le
      linarith [hfq u hu]
    have hH : |H| ≤ 3 * A ^ K := by
      have ht : |H| ≤ |H - q u| + |q u| := by
        convert abs_add_le (H - q u) (q u) using 1
        congr 1
        ring
      have ht' := mul_le_mul_of_nonneg_left hh1 (by positivity : 0 ≤ 2 * A ^ K)
      linarith [hq u hu]
    have htransfer : |evalAt S u w - evalAt S u (f u)| ≤ 2 * (A ^ K) ^ 3 * b :=
      (abs_hidden_quadratic_sub_le S hSdeg u hw hupp (hScurv u w)).trans
        (quadratic_transfer_le_cube hA0.le hM hAM hb hba)
    have hval : |evalAt (correctedPolynomial S f R a s L lam) u w| ≤ 13 * (A ^ K) ^ 3 * b := by
      rw [correctedPolynomial_eval]
      apply scalar_corrected_value_bound hM ha hb.le hh.le hah (hR u) htransfer
      · simpa only [baseTaylor_eval] using happrox u hu
      · exact hq u hu
      · exact hH
      · exact hLu
      · exact hlam
      · exact hclose
    have h13 : (13 : ℝ) ≤ A ^ 4 := by
      calc (13 : ℝ) ≤ 2 ^ 4 := by norm_num
           _ ≤ A ^ 4 := pow_le_pow_left₀ (by norm_num) hA 4
    have hvalpow : 13 * (A ^ K) ^ 3 ≤ A ^ C := by
      calc 13 * (A ^ K) ^ 3 ≤ A ^ 4 * (A ^ K) ^ 3 :=
             mul_le_mul_of_nonneg_right h13 (by positivity)
           _ = A ^ (3 * K + 4) := by rw [show 3 * K + 4 = K * 3 + 4 by omega, pow_add, pow_mul]; ring
           _ ≤ A ^ C := pow_le_pow_right₀ hA1 (by omega)
    have h14 : (14 : ℝ) ≤ A ^ 4 := by
      calc (14 : ℝ) ≤ 2 ^ 4 := by norm_num
           _ ≤ A ^ 4 := pow_le_pow_left₀ (by norm_num) hA 4
    have hderpow : 14 * (A ^ K) ^ 2 * A ≤ A ^ C := by
      calc 14 * (A ^ K) ^ 2 * A ≤ A ^ 4 * (A ^ K) ^ 2 * A := by gcongr
           _ = A ^ (2 * K + 5) := by rw [show 2 * K + 5 = K * 2 + 5 by omega, pow_add, pow_mul]; ring
           _ ≤ A ^ C := pow_le_pow_right₀ hA1 (by omega)
    have hscalea : A ^ C * (a * h) ≤ b := by
      have ht := (le_div_iff₀ ha).1 hscale
      nlinarith only [ht]
    have hprod : 14 * (A ^ K) ^ 2 * A * (a * h) ≤ b :=
      (mul_le_mul_of_nonneg_right hderpow (by positivity)).trans hscalea
    have h7 : 7 * (A ^ K) ^ 2 * (a * h) / b ≤ 1 / (2 * A) := by
      apply (div_le_div_iff₀ hb (by positivity : 0 < 2 * A)).2
      nlinarith only [hprod]
    have hasratio : a / s ≤ a * h / b := by
      apply (div_le_div_iff₀ hs hb).2
      have ht := mul_le_mul_of_nonneg_left hlarge.le ha.le
      exact ht.trans_eq (by ring)
    have hder : |a / s * (L u + 2 * lam * H)| ≤ 1 / (2 * A) := by
      refine (scalar_first_correction_bound hM ha.le hs hH hLu hlam).trans ?_
      calc 7 * (A ^ K) ^ 2 * (a / s) ≤ 7 * (A ^ K) ^ 2 * (a * h / b) :=
             mul_le_mul_of_nonneg_left hasratio (by positivity)
           _ = 7 * (A ^ K) ^ 2 * (a * h) / b := by ring
           _ ≤ 1 / (2 * A) := h7
    have htwoA : 2 * A ≤ A ^ C := by
      calc 2 * A ≤ A ^ 2 := by nlinarith only [hA, sq_nonneg (A - 2)]
           _ ≤ A ^ C := pow_le_pow_right₀ hA1 (by omega)
    have hfloor : A ^ (-(C : ℤ)) ≤ 1 / (2 * A) := by
      rw [zpow_neg, zpow_natCast]
      simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < 2 * A) htwoA
    have hlowQ : 1 / (2 * A) ≤ |evalAt (pderiv (3 : Fin 4)
        (correctedPolynomial S f R a s L lam)) u w| := by
      rw [correctedPolynomial_pderiv_eval]
      have ht : |evalAt (pderiv (3 : Fin 4) S) u w| ≤
          |evalAt (pderiv (3 : Fin 4) S) u w - a / s * (L u + 2 * lam * H)| +
            |a / s * (L u + 2 * lam * H)| := by
        convert abs_add_le (evalAt (pderiv (3 : Fin 4) S) u w - a / s * (L u + 2 * lam * H))
          (a / s * (L u + 2 * lam * H)) using 1
        congr 1
        ring
      have he : A⁻¹ = 2 * (1 / (2 * A)) := by field_simp
      change _ ≤ |evalAt (pderiv (3 : Fin 4) S) u w - a / s * (L u + 2 * lam * H)|
      linarith only [ht, he, hlow, hder]
    have huppQ : |evalAt (pderiv (3 : Fin 4)
        (correctedPolynomial S f R a s L lam)) u w| ≤ A ^ C := by
      rw [correctedPolynomial_pderiv_eval]
      change |evalAt (pderiv (3 : Fin 4) S) u w - a / s * (L u + 2 * lam * H)| ≤ A ^ C
      refine (abs_sub _ _).trans ?_
      have hunit : 1 / (2 * A) ≤ 1 := (div_le_one₀ (by positivity)).2 (by linarith)
      have hA2 : A + 1 ≤ A ^ 2 := by nlinarith only [hA, sq_nonneg (A - 2)]
      have hA2C : A ^ 2 ≤ A ^ C := pow_le_pow_right₀ hA1 (by omega)
      linarith only [hupp, hder, hunit, hA2, hA2C]
    have hcurvQ : |evalAt (pderiv (3 : Fin 4) (pderiv (3 : Fin 4)
        (correctedPolynomial S f R a s L lam))) u w| ≤ A ^ C / b := by
      rw [correctedPolynomial_pderiv_two_eval]
      refine (scalar_curvature_bound hA0.le hM0 hb hba has (hScurv u w) hlam).trans ?_
      apply div_le_div_of_nonneg_right _ hb.le
      have h3 : (3 : ℝ) ≤ A ^ 2 := by nlinarith only [hA, sq_nonneg (A - 2)]
      calc A + 2 * A ^ K ≤ 3 * A ^ K := by linarith
           _ ≤ A ^ 2 * A ^ K := mul_le_mul_of_nonneg_right h3 hM0
           _ = A ^ (K + 2) := by rw [pow_add]; ring
           _ ≤ A ^ C := pow_le_pow_right₀ hA1 (by omega)
    exact ⟨hval.trans (mul_le_mul_of_nonneg_right hvalpow hb.le), hfloor.trans hlowQ, huppQ, hcurvQ⟩

end Submission.Obl.k4_seven_direction_local_degree_restoration
