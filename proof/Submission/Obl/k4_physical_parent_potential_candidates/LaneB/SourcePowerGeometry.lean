import Submission.Obl.k4_physical_parent_potential_candidates.PhysicalSource

namespace Submission.Obl.k4_physical_parent_potential_candidates

noncomputable section

namespace SourceNormalization

/-- A single sufficiently large source power controls both the original
velocity geometry and the squared determinant floor of its seven samples. -/
theorem power_frame_bounds {K : ℝ} (hK : 2 ≤ K) {M : ℕ} (hM : 200 ≤ M) :
    2 ≤ K^M ∧ 32*K^4 ≤ K^M ∧ 1+2*K ≤ K^M ∧
      (K^M)⁻¹ ≤ (K^(-100:ℝ))^2 := by
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hbase : K ≤ K^M := by simpa using pow_le_pow_right₀ hK1 (by omega : 1 ≤ M)
  have h32 : (32:ℝ) ≤ K^5 := by
    exact (by norm_num : (32:ℝ) ≤ 2^5).trans (pow_le_pow_left₀ (by norm_num) hK 5)
  have hlarge : 32*K^4 ≤ K^M := by
    calc
      _ ≤ K^5*K^4 := mul_le_mul_of_nonneg_right h32 (by positivity)
      _ = K^9 := by ring
      _ ≤ K^M := pow_le_pow_right₀ hK1 (by omega)
  have hvel : 1+2*K ≤ K^M := by
    have hfour : 4 ≤ K^2 := by nlinarith only [hK]
    calc
      _ ≤ 4*K := by linarith only [hK]
      _ ≤ K^2*K := mul_le_mul_of_nonneg_right hfour hK0.le
      _ = K^3 := by ring
      _ ≤ K^M := pow_le_pow_right₀ hK1 (by omega)
  refine ⟨hK.trans hbase,hlarge,hvel,?_⟩
  have hdet : (K^(-100:ℝ))^2 = (K^200)⁻¹ := by
    rw [Real.rpow_neg hK0.le]
    norm_num [Real.rpow_natCast,←inv_pow,←pow_mul]
  rw [hdet]
  exact inv_anti₀ (pow_pos hK0 200) (pow_le_pow_right₀ hK1 hM)

/-- Convert the fixed source exponent to the normalized accuracy margin,
before any source or localization parameter is chosen. -/
theorem normalized_margin {K zeta w : ℝ} (M C : ℕ)
    (hmargin : K^(M*(2*C+40))*zeta ≤ w) :
    (K^M)^(2*C+40)*zeta ≤ w := by
  simpa only [←pow_mul] using hmargin

/-- The same margin supplies the initial discriminant smallness and the
branch regularity smallness for the actual extrapolated fit. -/
theorem source_curvature_bounds {A K a zeta w fit : ℝ}
    (hA : 2 ≤ A) (hK : 2 ≤ K) (hlarge : 32*K^4 ≤ A)
    (ha : 0 < a) (hzeta : 0 ≤ zeta) (hw : 0 < w) (hw1 : w ≤ 1)
    (haK : a ≤ K*zeta) (hfit : fit ≤ A*(a*w))
    (hmargin : A^2*zeta ≤ w) :
    32*K^3*(a*w) ≤ 1 ∧ 4*(K/2)*fit ≤ (2*(2*K)^2)⁻¹ := by
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hK0 : 0 < K := by linarith
  have hA2 : A ≤ A^2 := by simpa using pow_le_pow_right₀ hA1 (by decide : 1 ≤ 2)
  have hAzeta : A*zeta ≤ w :=
    (mul_le_mul_of_nonneg_right hA2 hzeta).trans hmargin
  have h16 : 16*K^4 ≤ A := by
    have hp := pow_nonneg hK0.le 4
    linarith only [hlarge,hp]
  have hfirst : 32*K^3*(a*w) ≤ 1 := by
    calc
      _ ≤ 32*K^3*((K*zeta)*w) := by gcongr
      _ = (32*K^4)*(zeta*w) := by ring
      _ ≤ A*(zeta*w) := by gcongr
      _ = (A*zeta)*w := by ring
      _ ≤ w*w := mul_le_mul_of_nonneg_right hAzeta hw.le
      _ ≤ 1 := by nlinarith only [hw.le,hw1]
  have hfitSmall : 16*K^3*fit ≤ 1 := by
    calc
      _ ≤ 16*K^3*(A*(a*w)) := by gcongr
      _ ≤ 16*K^3*(A*((K*zeta)*w)) := by gcongr
      _ = (16*K^4)*A*(zeta*w) := by ring
      _ ≤ A*A*(zeta*w) := by gcongr
      _ = (A^2*zeta)*w := by ring
      _ ≤ w*w := mul_le_mul_of_nonneg_right hmargin hw.le
      _ ≤ 1 := by nlinarith only [hw.le,hw1]
  refine ⟨hfirst,?_⟩
  rw [←one_div,le_div_iff₀ (by positivity : 0 < 2*(2*K)^2)]
  convert hfitSmall using 1 <;> ring

end SourceNormalization

end

end Submission.Obl.k4_physical_parent_potential_candidates
