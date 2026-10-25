import Mathlib
set_option autoImplicit false
namespace Submission.Obl.k4_scalar_pair_atlas_assembly

/-- One exponent controls old assignments, their finite unions, and the representative table. -/
def installComplexity (B G : ℕ) : ℕ := 2 * B + G + 4

lemma old_le_installComplexity (B G : ℕ) : B ≤ installComplexity B G := by
  unfold installComplexity
  omega
lemma table_le_installComplexity (B G : ℕ) : G ≤ installComplexity B G := by
  unfold installComplexity
  omega
lemma installComplexity_pos (B G : ℕ) : 1 ≤ installComplexity B G := by
  unfold installComplexity
  omega

lemma install_format_budget {N : ℝ} (hN : 2 ≤ N) (B G n : ℕ)
    (hn : (n : ℝ) ≤ N ^ (B : ℝ)) :
    2 * (n : ℝ) * N ^ (B : ℝ) + 5 ≤ N ^ (installComplexity B G : ℝ) := by
  simp only [Real.rpow_natCast] at hn ⊢
  have hN₁ : 1 ≤ N := by linarith
  have hN₀ : 0 ≤ N := by linarith
  have hb : 1 ≤ N ^ (2 * B) := one_le_pow₀ hN₁
  have hfour : (16 : ℝ) ≤ N ^ 4 := by
    calc
      16 = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ N ^ 4 := by gcongr
  have hp := mul_le_mul_of_nonneg_right hn (pow_nonneg hN₀ B)
  have hpow : N ^ B * N ^ B = N ^ (2 * B) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at hp
  calc
    2 * (n : ℝ) * N ^ B + 5 ≤ 2 * N ^ (2 * B) + 5 := by nlinarith
    _ ≤ N ^ (2 * B + 4) := by
      rw [pow_add]
      nlinarith
    _ ≤ N ^ installComplexity B G :=
      pow_le_pow_right₀ hN₁ (by unfold installComplexity; omega)

end Submission.Obl.k4_scalar_pair_atlas_assembly
