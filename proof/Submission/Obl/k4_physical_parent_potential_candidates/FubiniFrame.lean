import Submission.Obl.k4_physical_parent_potential_candidates.FubiniAlgebra

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set

noncomputable section

/-- The moving quadric, in terms of displacement from the moving tangent plane. -/
def fubiniFrameValue (rho k B n lam : ℝ) : ℝ := rho*(2*k-B-2*n*k-lam*k^2)

def fubiniFrameVertical (rho k n lam : ℝ) : ℝ := rho*(2-2*n-2*lam*k)

/-- All large terms cancel in the moving quadric derivative. Only the
three Fubini defects remain. -/
theorem hasDerivAt_fubiniFrameValue
    {rho k B n lam : ℝ → ℝ} {t mv v E T W : ℝ}
    (hrho : HasDerivAt rho (-rho t*mv) t)
    (hk : HasDerivAt k (-v) t)
    (hB : HasDerivAt B (mv*B t+2*n t*v+E-2*v) t)
    (hn : HasDerivAt n (mv*n t+lam t*v+T-mv) t)
    (hlam : HasDerivAt lam (lam t*mv+W) t) :
    HasDerivAt (fun s => fubiniFrameValue (rho s) (k s) (B s) (n s) (lam s))
      (-rho t*(E+2*T*k t+W*(k t)^2)) t := by
  convert hrho.mul ((((hk.const_mul 2).sub hB).sub ((hn.const_mul 2).mul hk)).sub
    (hlam.mul (hk.pow 2))) using 1 <;> (try funext s) <;> dsimp [fubiniFrameValue] <;> ring

/-- The same cancellation preserves the vertical derivative, rather than
merely controlling the quadric's values. -/
theorem hasDerivAt_fubiniFrameVertical
    {rho k n lam : ℝ → ℝ} {t mv v T W : ℝ}
    (hrho : HasDerivAt rho (-rho t*mv) t)
    (hk : HasDerivAt k (-v) t)
    (hn : HasDerivAt n (mv*n t+lam t*v+T-mv) t)
    (hlam : HasDerivAt lam (lam t*mv+W) t) :
    HasDerivAt (fun s => fubiniFrameVertical (rho s) (k s) (n s) (lam s))
      (-2*rho t*(T+W*k t)) t := by
  convert hrho.mul (((hasDerivAt_const t (2:ℝ)).sub (hn.const_mul 2)).sub
    ((hlam.const_mul 2).mul hk)) using 1 <;> (try funext s) <;> dsimp [fubiniFrameVertical] <;> ring

private theorem frame_value_derivative_bound
    {K ε rho k E T W : ℝ} (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hrho : |rho| ≤ K) (hk : |k| ≤ 5*K)
    (hE : |E| ≤ 27*ε) (hT : |T| ≤ 9*ε) (hW : |W| ≤ 3*ε) :
    |-rho*(E+2*T*k+W*k^2)| ≤ 1000*K^3*ε := by
  have hK0 : 0 ≤ K := by linarith
  have hin : |E+2*T*k+W*k^2| ≤ 27*ε+2*(9*ε)*(5*K)+(3*ε)*(5*K)^2 := by
    calc
      _ ≤ |E|+|2*T*k|+|W*k^2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by
        simp only [abs_mul, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        gcongr
  rw [abs_mul, abs_neg]
  calc
    _ ≤ K*(27*ε+2*(9*ε)*(5*K)+(3*ε)*(5*K)^2) :=
      mul_le_mul hrho hin (abs_nonneg _) hK0
    _ = (27*K+90*K^2+75*K^3)*ε := by ring
    _ ≤ 1000*K^3*ε := by
      apply mul_le_mul_of_nonneg_right ?_ hε
      have h1 : K ≤ K^3 := by simpa using pow_le_pow_right₀ hK (by decide : 1 ≤ 3)
      have h2 : K^2 ≤ K^3 := pow_le_pow_right₀ hK (by decide : 2 ≤ 3)
      nlinarith [pow_nonneg hK0 3]

private theorem frame_vertical_derivative_bound
    {K ε rho k T W : ℝ} (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hrho : |rho| ≤ K) (hk : |k| ≤ 5*K)
    (hT : |T| ≤ 9*ε) (hW : |W| ≤ 3*ε) :
    |-2*rho*(T+W*k)| ≤ 1000*K^3*ε := by
  have hK0 : 0 ≤ K := by linarith
  have hin : |T+W*k| ≤ 9*ε+(3*ε)*(5*K) := by
    exact (abs_add_le _ _).trans (add_le_add hT (by rw [abs_mul]; gcongr))
  rw [abs_mul, abs_mul, abs_neg]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 2)]
  calc
    _ ≤ 2*K*(9*ε+(3*ε)*(5*K)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hrho (by norm_num)) hin (abs_nonneg _) (by positivity)
    _ = (18*K+30*K^2)*ε := by ring
    _ ≤ 1000*K^3*ε := by
      apply mul_le_mul_of_nonneg_right ?_ hε
      have h1 : K ≤ K^3 := by simpa using pow_le_pow_right₀ hK (by decide : 1 ≤ 3)
      have h2 : K^2 ≤ K^3 := pow_le_pow_right₀ hK (by decide : 2 ≤ 3)
      nlinarith [pow_nonneg hK0 3]

/-- Freeze the moving quadric at the beginning of a unit segment. Both
its value and its vertical derivative change linearly in the Fubini defects. -/
theorem freeze_fubini_frame
    (rho k B n lam mv v E T W : ℝ → ℝ)
    {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hrho : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt rho (-rho t*mv t) t)
    (hk : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt k (-v t) t)
    (hB : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt B (mv t*B t+2*n t*v t+E t-2*v t) t)
    (hn : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt n (mv t*n t+lam t*v t+T t-mv t) t)
    (hlam : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt lam (lam t*mv t+W t) t)
    (hrhob : ∀ t ∈ Icc (0:ℝ) 1, |rho t| ≤ K)
    (hkb : ∀ t ∈ Icc (0:ℝ) 1, |k t| ≤ 5*K)
    (hEb : ∀ t ∈ Icc (0:ℝ) 1, |E t| ≤ 27*ε)
    (hTb : ∀ t ∈ Icc (0:ℝ) 1, |T t| ≤ 9*ε)
    (hWb : ∀ t ∈ Icc (0:ℝ) 1, |W t| ≤ 3*ε) :
    |fubiniFrameValue (rho 1) (k 1) (B 1) (n 1) (lam 1)-
      fubiniFrameValue (rho 0) (k 0) (B 0) (n 0) (lam 0)| ≤ 1000*K^3*ε ∧
    |fubiniFrameVertical (rho 1) (k 1) (n 1) (lam 1)-
      fubiniFrameVertical (rho 0) (k 0) (n 0) (lam 0)| ≤ 1000*K^3*ε := by
  have hval := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hasDerivAt_fubiniFrameValue (hrho t ht) (hk t ht)
      (hB t ht) (hn t ht) (hlam t ht)).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using
      frame_value_derivative_bound hK hε (hrhob t ht) (hkb t ht) (hEb t ht) (hTb t ht) (hWb t ht))
    (convex_Icc (0:ℝ) 1) (by simp : (0:ℝ) ∈ Icc (0:ℝ) 1) (by simp : (1:ℝ) ∈ Icc (0:ℝ) 1)
  have hver := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hasDerivAt_fubiniFrameVertical (hrho t ht) (hk t ht)
      (hn t ht) (hlam t ht)).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using
      frame_vertical_derivative_bound hK hε (hrhob t ht) (hkb t ht) (hTb t ht) (hWb t ht))
    (convex_Icc (0:ℝ) 1) (by simp : (0:ℝ) ∈ Icc (0:ℝ) 1) (by simp : (1:ℝ) ∈ Icc (0:ℝ) 1)
  exact ⟨by simpa only [Real.norm_eq_abs, sub_zero, norm_one, mul_one] using hval,
    by simpa only [Real.norm_eq_abs, sub_zero, norm_one, mul_one] using hver⟩

end

end Submission.Obl.k4_physical_parent_potential_candidates
