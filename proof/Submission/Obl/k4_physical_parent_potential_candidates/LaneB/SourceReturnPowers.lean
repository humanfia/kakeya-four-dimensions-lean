import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourcePowerGeometry

namespace Submission.Obl.k4_physical_parent_potential_candidates

noncomputable section

namespace SourceNormalization

def returnTime (A : ℝ) (C : ℕ) : ℝ := (A^(2*C+10))⁻¹

def returnLoss (A : ℝ) (C J : ℕ) : ℝ := A^(6*C+J+60)

def returnLocalLoss (A Eb a w : ℝ) (C : ℕ) : ℝ :=
  max (2*A^C*Eb/(a*w)) (max (A^C) (A^C*(a*w)/Eb))

/-- Quantitative bounds for returning the local normalized certificate
to the entire original time block. -/
theorem source_return_powers {A lam Cm Eb a w : ℝ} (C J : ℕ)
    (hA : 2 ≤ A) (hlam : 0 ≤ lam) (hlamA : lam ≤ A)
    (haw : 0 < a*w) (hwidth : a*w ≤ Eb)
    (hEb : Eb ≤ A^(C+31)*(a*w)) (hCm : Cm ≤ A^J) :
    0 < returnTime A C ∧ returnTime A C ≤ 1/2 ∧
    lam*returnTime A C ≤ (A^C)⁻¹ ∧
    max Cm (returnLocalLoss A Eb a w C) ≤ returnLoss A C J ∧
    32*returnLocalLoss A Eb a w C/(returnTime A C)^2 ≤ returnLoss A C J := by
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hEb0 : 0 < Eb := haw.trans_le hwidth
  have ht0 : 0 < returnTime A C := by dsimp only [returnTime]; positivity
  have ht2 : returnTime A C ≤ 1/2 := by
    dsimp only [returnTime]
    rw [one_div]
    exact inv_anti₀ (by norm_num) (hA.trans (by
      simpa using pow_le_pow_right₀ hA1 (by omega : 1 ≤ 2*C+10)))
  have hstep : lam*returnTime A C ≤ (A^C)⁻¹ := by
    calc
      _ ≤ A*returnTime A C := mul_le_mul_of_nonneg_right hlamA ht0.le
      _ = A/A^(2*C+10) := by simp only [returnTime,div_eq_mul_inv]
      _ ≤ 1/A^C := by
        rw [div_le_div_iff₀ (pow_pos hA0 _) (pow_pos hA0 _),one_mul]
        simpa only [pow_succ'] using pow_le_pow_right₀ hA1 (by omega : C+1 ≤ 2*C+10)
      _ = _ := one_div _
  have hloc : returnLocalLoss A Eb a w C ≤ A^(2*C+32) := by
    dsimp only [returnLocalLoss]
    apply max_le
    · rw [div_le_iff₀ haw]
      calc
        _ ≤ 2*A^C*(A^(C+31)*(a*w)) := by gcongr
        _ ≤ A*A^C*(A^(C+31)*(a*w)) := by gcongr
        _ = _ := by simp only [pow_add,pow_mul]; ring
    · apply max_le
      · exact pow_le_pow_right₀ hA1 (by omega)
      · rw [div_le_iff₀ hEb0]
        exact (mul_le_mul_of_nonneg_left hwidth (by positivity)).trans
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA1 (by omega)) hEb0.le)
  have hCr : max Cm (returnLocalLoss A Eb a w C) ≤ returnLoss A C J := by
    exact max_le (hCm.trans (pow_le_pow_right₀ hA1 (by omega)))
      (hloc.trans (pow_le_pow_right₀ hA1 (by omega)))
  refine ⟨ht0,ht2,hstep,hCr,?_⟩
  have h32 : (32:ℝ) ≤ A^5 :=
    (by norm_num : (32:ℝ) ≤ 2^5).trans (pow_le_pow_left₀ (by norm_num) hA 5)
  have hloc0 : 0 ≤ returnLocalLoss A Eb a w C := by
    dsimp only [returnLocalLoss]
    positivity
  rw [returnTime,div_eq_mul_inv,inv_pow,inv_inv]
  calc
    _ ≤ A^5*A^(2*C+32)*(A^(2*C+10))^2 := by gcongr
    _ = A^(6*C+57) := by simp only [pow_add,pow_mul]; ring
    _ ≤ _ := pow_le_pow_right₀ hA1 (by omega : 6*C+57 ≤ 6*C+J+60)

/-- The source tube interval fits inside the extrapolated original-chart
window, and so does the eventual shorter return interval. -/
theorem source_time_windows {A K lam h : ℝ} (C : ℕ)
    (hK : 2 ≤ K) (hlarge : 32*K^4 ≤ A) (hlam : 1 ≤ lam) (hh : 0 < h) :
    (8*K*h)/(8*A*lam) ≤ h/(4*K^2) ∧
      returnTime A C*h ≤ h/(4*K^2) := by
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hA0 : 0 < A := (by positivity : 0 < 32*K^4).trans_le hlarge
  have hLam0 : 0 < lam := by linarith
  have hK2 : 1 ≤ K^2 := one_le_pow₀ hK1
  have h2 : 4*K^2 ≤ A := by
    have hp : 0 ≤ K^2*(K^2-1) := mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hK2)
    nlinarith only [hlarge,hK2,hp]
  have h3 : 4*K^3 ≤ A := by
    have hp : K^3 ≤ K^4 := pow_le_pow_right₀ hK1 (by decide : 3 ≤ 4)
    have hp0 := pow_nonneg hK0.le 4
    linarith only [hlarge,hp,hp0]
  have hA2 : 2 ≤ A := by
    nlinarith only [hK2,h2]
  constructor
  · rw [div_le_div_iff₀ (by positivity : 0 < 8*A*lam) (by positivity : 0 < 4*K^2)]
    have hprod : 4*K^3 ≤ A*lam := h3.trans (le_mul_of_one_le_right hA0.le hlam)
    nlinarith only [mul_le_mul_of_nonneg_right hprod hh.le]
  · have hpow : 4*K^2 ≤ A^(2*C+10) := h2.trans (by
      simpa using pow_le_pow_right₀ (by linarith : 1 ≤ A) (by omega : 1 ≤ 2*C+10))
    have hinv := inv_anti₀ (by positivity : 0 < 4*K^2) hpow
    calc
      _ ≤ (4*K^2)⁻¹*h := mul_le_mul_of_nonneg_right hinv hh.le
      _ = _ := by ring

end SourceNormalization

end

end Submission.Obl.k4_physical_parent_potential_candidates
