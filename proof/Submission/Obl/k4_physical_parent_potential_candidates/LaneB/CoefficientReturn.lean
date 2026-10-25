import Submission.Obl.k4_physical_parent_potential_candidates.MainHelpers

namespace Submission.Obl.k4_physical_parent_potential_candidates

noncomputable section

/-- Returning a vertically normalized graph may cost the inverse target
thickness in its coefficients. This factor is paid entirely by the freely
chosen coefficient format, with no change to the value or mass budget. -/
theorem restored_coeff_with_inverse_le
    {N K C0 G L r ρ a w Cr : ℝ} {Mp Mr Ecoef Mi : ℕ}
    (hN : 2 ≤ N) (hC0 : C0 ≤ N) (hK0 : 0 ≤ K) (hK : K ≤ N^⌈G⌉₊)
    (hG : 0 ≤ G) (hrL : r ≤ L) (hρ : 0 ≤ ρ)
    (ha : 0 < a) (halo : N^(-r) ≤ a) (hCr : 0 < Cr) (hCrN : Cr ≤ N^⌈G⌉₊)
    (hw : w = N^(-((1-ρ)*G))/(4*Cr))
    (hMi : Ecoef*(⌈L⌉₊+3*⌈G⌉₊+Mp+Mr+4)+1 ≤ Mi) :
    C0*(K*N^(Mp+Mr+1)*(1+(a*w)⁻¹))^Ecoef ≤ N^Mi := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hw0 : 0 < w := by rw [hw]; positivity
  have haI : a⁻¹ ≤ N^r := by
    calc a⁻¹ ≤ (N^(-r))⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hN0 _) halo
      _ = N^r := by rw [← Real.rpow_neg hN0.le]; congr 1; ring
  have hrpow : N^r ≤ N^⌈L⌉₊ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (hrL.trans (Nat.le_ceil L))
  have hGpow : N^((1-ρ)*G) ≤ N^⌈G⌉₊ := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    nlinarith [Nat.le_ceil G, mul_nonneg hρ hG]
  have hwI : (a*w)⁻¹ = a⁻¹*(4*Cr)*N^((1-ρ)*G) := by
    rw [hw, mul_inv, inv_div, Real.rpow_neg hN0.le, div_inv_eq_mul]
    ring
  have h4 : (4:ℝ) ≤ N^2 := by nlinarith
  have hinv : (a*w)⁻¹ ≤ N^(⌈L⌉₊+2*⌈G⌉₊+2) := by
    rw [hwI]
    calc a⁻¹*(4*Cr)*N^((1-ρ)*G)
        ≤ N^⌈L⌉₊*(N^2*N^⌈G⌉₊)*N^⌈G⌉₊ := by
          apply mul_le_mul (mul_le_mul (haI.trans hrpow)
            (mul_le_mul h4 hCrN hCr.le (by positivity))
            (by positivity) (by positivity)) hGpow (by positivity) (by positivity)
      _ = N^(⌈L⌉₊+2*⌈G⌉₊+2) := by
          simp only [← pow_add]
          congr 1
          omega
  have hone : 1 ≤ N^(⌈L⌉₊+2*⌈G⌉₊+2) := one_le_pow₀ hN1
  have hsum : 1+(a*w)⁻¹ ≤ N^(⌈L⌉₊+2*⌈G⌉₊+3) := by
    calc 1+(a*w)⁻¹ ≤ 2*N^(⌈L⌉₊+2*⌈G⌉₊+2) := by linarith
      _ ≤ N*N^(⌈L⌉₊+2*⌈G⌉₊+2) :=
        mul_le_mul_of_nonneg_right hN (by positivity)
      _ = N^(⌈L⌉₊+2*⌈G⌉₊+3) :=
        (pow_succ' N (⌈L⌉₊+2*⌈G⌉₊+2)).symm.trans
          (congrArg (fun n:ℕ => N^n) (by omega))
  have hbase : K*N^(Mp+Mr+1)*(1+(a*w)⁻¹) ≤
      N^(⌈L⌉₊+3*⌈G⌉₊+Mp+Mr+4) := by
    calc _ ≤ N^⌈G⌉₊*N^(Mp+Mr+1)*N^(⌈L⌉₊+2*⌈G⌉₊+3) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right hK (by positivity)) hsum
              (by positivity) (by positivity)
      _ = _ := by simp only [← pow_add]; congr 1; omega
  calc _ ≤ N*(N^(⌈L⌉₊+3*⌈G⌉₊+Mp+Mr+4))^Ecoef := by
          exact mul_le_mul hC0 (pow_le_pow_left₀ (by positivity) hbase Ecoef)
            (by positivity) (by positivity)
    _ = N^(Ecoef*(⌈L⌉₊+3*⌈G⌉₊+Mp+Mr+4)+1) := by
          rw [← pow_mul]
          simpa only [Nat.mul_comm] using
            (pow_succ' N ((⌈L⌉₊+3*⌈G⌉₊+Mp+Mr+4)*Ecoef)).symm
    _ ≤ N^Mi := pow_le_pow_right₀ hN1 hMi

end

end Submission.Obl.k4_physical_parent_potential_candidates
