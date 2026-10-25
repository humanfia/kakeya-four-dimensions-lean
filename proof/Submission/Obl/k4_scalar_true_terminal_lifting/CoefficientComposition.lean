import Submission.Obl.k4_scalar_true_terminal_lifting.ScalarComposition
import Submission.Obl.k4_scalar_true_terminal_lifting.Poly

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MvPolynomial

theorem two_mul_rpow_le {N : ℝ} (hN : 2 ≤ N) (a : ℝ) :
    2 * N ^ a ≤ N ^ (a + 1) := by
  have hN₀ : 0 < N := by linarith
  calc
    2 * N ^ a ≤ N * N ^ a :=
      mul_le_mul_of_nonneg_right hN (Real.rpow_pos_of_pos hN₀ _).le
    _ = N ^ (a + 1) := by rw [Real.rpow_add hN₀, Real.rpow_one]; ring

/-- Bounds for the two rows of the affine substitution have a fixed exponent
depending on the parent horizon and inverse transverse scale. -/
theorem affine_substitution_power_bounds {N H B t₀ dt u v J : ℝ}
    (hN : 2 ≤ N) (hH : 0 ≤ H) (hB : 0 ≤ B)
    (htime : |dt⁻¹| ≤ N ^ H) (ht₀ : |t₀| ≤ 1)
    (hJ : |J⁻¹| ≤ N ^ B) (hcenter : |u| + |v| ≤ N) :
    |dt⁻¹| * (1 + |t₀|) ≤ N ^ (H + B + 2) ∧
      |J⁻¹| * (1 + |u| + |v|) ≤ N ^ (H + B + 2) := by
  have hN₀ : 0 < N := by linarith
  have hN₁ : 1 ≤ N := by linarith
  constructor
  · calc
      _ ≤ N ^ H * (1 + 1) :=
        mul_le_mul htime (by linarith) (by positivity) (by positivity)
      _ = 2 * N ^ H := by ring
      _ ≤ N ^ (H + 1) := two_mul_rpow_le hN H
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith)
  · calc
      _ ≤ N ^ B * (2 * N) :=
        mul_le_mul hJ (by linarith) (by positivity) (by positivity)
      _ = 2 * N ^ (B + 1) := by rw [Real.rpow_add hN₀, Real.rpow_one]; ring
      _ ≤ N ^ (B + 1 + 1) := two_mul_rpow_le hN (B + 1)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith)

/-- A single fixed integer increment absorbs the coefficient-count constants. -/
theorem quadratic_coefficient_power_bound {N α β d : ℝ}
    (hN : 2 ≤ N) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hd : 0 ≤ d) :
    9 * N ^ α + 9 * N ^ β * (N ^ d) ^ 2 ≤ N ^ (α + β + 2 * d + 5) := by
  have hN₀ : 0 < N := by linarith
  have hN₁ : 1 ≤ N := by linarith
  have h₀ : N ^ α ≤ N ^ (α + β + 2 * d) :=
    Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith)
  have heq : N ^ β * (N ^ d) ^ 2 = N ^ (β + 2 * d) := by
    rw [pow_two, ← Real.rpow_add hN₀, ← Real.rpow_add hN₀]
    congr 1
    ring
  have h₁ : N ^ β * (N ^ d) ^ 2 ≤ N ^ (α + β + 2 * d) := by
    rw [heq]
    exact Real.rpow_le_rpow_of_exponent_le hN₁ (by linarith)
  have h18 : (18 : ℝ) ≤ N ^ (5 : ℝ) := by
    change (18 : ℝ) ≤ N ^ ((5 : ℕ) : ℝ)
    rw [Real.rpow_natCast]
    exact (by norm_num : (18 : ℝ) ≤ 2 ^ 5).trans
      (pow_le_pow_left₀ (by norm_num) hN 5)
  calc
    _ = 9 * N ^ α + 9 * (N ^ β * (N ^ d) ^ 2) := by ring
    _ ≤ 9 * N ^ (α + β + 2 * d) + 9 * N ^ (α + β + 2 * d) :=
      add_le_add (mul_le_mul_of_nonneg_left h₀ (by norm_num))
        (mul_le_mul_of_nonneg_left h₁ (by norm_num))
    _ = 18 * N ^ (α + β + 2 * d) := by ring
    _ ≤ N ^ (5 : ℝ) * N ^ (α + β + 2 * d) :=
      mul_le_mul_of_nonneg_right h18 (Real.rpow_pos_of_pos hN₀ _).le
    _ = _ := by rw [← Real.rpow_add hN₀]; congr 1; ring

theorem chartBaseSubstitution_time_cnorm (t₀ dt u v J : ℝ) :
    cnorm (chartBaseSubstitution t₀ dt u v J 0) ≤ |dt⁻¹| * (1 + |t₀|) := by
  apply (cnorm_C_mul_le _ _).trans
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  simpa only [cnorm_X, cnorm_C] using
    cnorm_sub_le (X 0 : MvPolynomial (Fin 2) ℝ) (C t₀)

theorem chartBaseSubstitution_space_cnorm (t₀ dt u v J : ℝ) :
    cnorm (chartBaseSubstitution t₀ dt u v J 1) ≤ |J⁻¹| * (1 + |u| + |v|) := by
  apply (cnorm_C_mul_le _ _).trans
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (cnorm_sub_le _ _).trans
    ((add_le_add (cnorm_sub_le _ _) (cnorm_C_mul_le v (X 0))).trans_eq
      (by simp only [cnorm_X, cnorm_C, mul_one]))

/-- A degree-two child predictor costs only a quadratic power of a uniform
coefficient bound for the affine base substitution. -/
theorem composedPotential_cnorm {P₀ P₁ : MvPolynomial (Fin 2) ℝ}
    (hP₁ : P₁.totalDegree ≤ 2) (t₀ dt u v J s R : ℝ) (hR : 1 ≤ R)
    (htime : |dt⁻¹| * (1 + |t₀|) ≤ R)
    (hspace : |J⁻¹| * (1 + |u| + |v|) ≤ R) :
    cnorm (composedPotential P₀ P₁ t₀ dt u v J s) ≤
      cnorm P₀ + |s| * cnorm P₁ * R ^ 2 := by
  have hsub : ∀ e, cnorm (chartBaseSubstitution t₀ dt u v J e) ≤ R := by
    intro e
    fin_cases e
    · exact (chartBaseSubstitution_time_cnorm _ _ _ _ _).trans htime
    · exact (chartBaseSubstitution_space_cnorm _ _ _ _ _).trans hspace
  have hp := cnorm_bind₁_le _ hR hsub P₁
  have hpow := pow_le_pow_right₀ hR hP₁
  unfold composedPotential
  apply (cnorm_add_le _ _).trans
  apply add_le_add le_rfl
  apply (cnorm_C_mul_le _ _).trans
  exact (mul_le_mul_of_nonneg_left
    (hp.trans (mul_le_mul_of_nonneg_left hpow (cnorm_nonneg _))) (abs_nonneg _)).trans_eq
      (by ring)

/-- The coefficient bound for the actual composed potential is explicit;
unlike sign-format tests, this polynomial is never rescaled. -/
theorem composedPotential_coeff {P₀ P₁ : MvPolynomial (Fin 2) ℝ}
    (hP₀ : P₀.totalDegree ≤ 2) (hP₁ : P₁.totalDegree ≤ 2)
    {B₀ B₁ : ℝ} (hc₀ : ∀ a, |P₀.coeff a| ≤ B₀) (hc₁ : ∀ a, |P₁.coeff a| ≤ B₁)
    (t₀ dt u v J s R : ℝ) (hR : 1 ≤ R)
    (htime : |dt⁻¹| * (1 + |t₀|) ≤ R)
    (hspace : |J⁻¹| * (1 + |u| + |v|) ≤ R)
    (a : Fin 2 →₀ ℕ) :
    |(composedPotential P₀ P₁ t₀ dt u v J s).coeff a| ≤
      9 * B₀ + |s| * (9 * B₁) * R ^ 2 := by
  have h₀ : cnorm P₀ ≤ 9 * B₀ := by simpa using cnorm_le_of_coeff P₀ hP₀ hc₀
  have h₁ : cnorm P₁ ≤ 9 * B₁ := by simpa using cnorm_le_of_coeff P₁ hP₁ hc₁
  apply (abs_coeff_le_cnorm _ _).trans
  apply (composedPotential_cnorm hP₁ t₀ dt u v J s R hR htime hspace).trans
  exact add_le_add h₀ (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left h₁ (abs_nonneg _)) (sq_nonneg _))

/-- Uniform power bounds on the input polynomials and affine substitutions
give one fixed output exponent. -/
theorem composedPotential_fixed_coeff {P₀ P₁ : MvPolynomial (Fin 2) ℝ}
    (hP₀ : P₀.totalDegree ≤ 2) (hP₁ : P₁.totalDegree ≤ 2)
    {N α β d : ℝ} (hN : 2 ≤ N) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hd : 0 ≤ d)
    (hc₀ : ∀ a, |P₀.coeff a| ≤ N ^ α) (hc₁ : ∀ a, |P₁.coeff a| ≤ N ^ β)
    (t₀ dt u v J s : ℝ) (hs : |s| ≤ 1)
    (htime : |dt⁻¹| * (1 + |t₀|) ≤ N ^ d)
    (hspace : |J⁻¹| * (1 + |u| + |v|) ≤ N ^ d)
    (a : Fin 2 →₀ ℕ) :
    |(composedPotential P₀ P₁ t₀ dt u v J s).coeff a| ≤ N ^ (α + β + 2 * d + 5) := by
  have hN₀ : 0 < N := by linarith
  have hR : 1 ≤ N ^ d := Real.one_le_rpow (by linarith) hd
  apply (composedPotential_coeff hP₀ hP₁ hc₀ hc₁ t₀ dt u v J s (N ^ d)
    hR htime hspace a).trans
  apply le_trans _ (quadratic_coefficient_power_bound hN hα hβ hd)
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_right
    (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hs (show 0 ≤ 9 * N ^ β by positivity)) (sq_nonneg _)

end Submission.Obl.k4_scalar_true_terminal_lifting
