import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticPolynomial
import Submission.Obl.k4_scalar_initial_true_horizon.InitialAsymptotic

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ProjectedCoefficients.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Set Filter MvPolynomial

noncomputable section

/-- The moving-interval norm controls the original coefficients, with an
explicit loss for the inverse width. -/
theorem projected_coefficients_of_moving_norm
    (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2)
    {H V u v β : ℝ} (hH : 1 ≤ H) (hV : 1 ≤ V)
    (hcenter : |u| + |v| ≤ H) (hβ : 0 < β) (hβinv : β⁻¹ ≤ V)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (-1 : ℝ) 1,
      |eval ![t, u + t * v + β * z] G| ≤ H) :
    ∀ e, |G.coeff e| ≤ 240 * (H * V) ^ 5 := by
  have hHH : H ≤ H * V := le_mul_of_one_le_right (by linarith) hV
  have hVV : V ≤ H * V := le_mul_of_one_le_left (by linarith) hH
  obtain ⟨c, hc, hcb⟩ :=
    Submission.Obl.k4_fixed_budget_quadratic_recovery.adapted_quadratic_coefficients
      G hG (hH.trans hHH) (hcenter.trans hHH) hβ (hβinv.trans hVV)
      (fun t ht z hz => (hbound t ht z hz).trans hHH)
  rw [Submission.Obl.k4_fixed_budget_quadratic_recovery.polynomial_eq_of_quadratic_values hc]
  intro e
  have hh := Submission.Obl.k4_fixed_budget_quadratic_recovery.quadraticPolynomial_coeff_bound
    (by positivity : 0 ≤ 40 * (H * V) ^ 5) hcb e
  convert hh using 1 <;> ring

/-- A single fixed power bounds every polynomial in every projected layer
whose width is at least `N^-B/H`. The bound is independent of the intercept
and velocity mesh used to prepare those layers. -/
theorem eventually_projected_coefficients_with_loss
    {N H : ℕ → ℝ} (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : ∀ k, 1 ≤ H k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε)
    {B η : ℝ} (hB : 0 ≤ B) (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ (G : MvPolynomial (Fin 2) ℝ) (u v β : ℝ),
      G.totalDegree ≤ 2 → |u| + |v| ≤ H k → 0 < β →
      N k ^ (-B) / H k ≤ β →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (-1 : ℝ) 1,
        |eval ![t, u + t * v + β * z] G| ≤ H k) →
      ∀ e, |G.coeff e| ≤ N k ^ (η + 5 * B) := by
  filter_upwards [hsub (η / 20) (by positivity),
    Submission.Obl.k4_scalar_initial_true_horizon.eventually_const_le_rpow
      hNt (by positivity : (0 : ℝ) < η / 2) 240] with k hsmall hconst
  intro G u v β hG hcenter hβ hβlo hbound e
  have hNp : 0 < N k := by linarith [hN k]
  have hN1 : 1 ≤ N k := by linarith [hN k]
  have hHp : 0 < H k := by linarith [hH k]
  have hV : 1 ≤ H k * N k ^ B :=
    (hH k).trans (le_mul_of_one_le_right hHp.le (Real.one_le_rpow hN1 hB))
  have hβinv : β⁻¹ ≤ H k * N k ^ B := by
    have hh := one_div_le_one_div_of_le (div_pos (Real.rpow_pos_of_pos hNp _) hHp) hβlo
    simpa only [one_div, inv_div, Real.rpow_neg hNp.le, div_inv_eq_mul] using hh
  have hc := projected_coefficients_of_moving_norm G hG (hH k) hV hcenter hβ hβinv hbound e
  calc
    _ ≤ 240 * (H k * (H k * N k ^ B)) ^ 5 := hc
    _ ≤ 240 * (N k ^ (η / 20) * (N k ^ (η / 20) * N k ^ B)) ^ 5 := by
      gcongr
    _ = 240 * N k ^ (η / 2 + 5 * B) := by
      rw [← Real.rpow_add hNp, ← Real.rpow_add hNp, ← Real.rpow_mul_natCast hNp.le]
      congr 2
      ring
    _ ≤ N k ^ (η / 2) * N k ^ (η / 2 + 5 * B) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hNp.le _)
    _ = N k ^ (η + 5 * B) := by
      rw [← Real.rpow_add hNp]
      congr 1
      ring

/-- A fixed convenient coefficient exponent, when no later mesh budget
requires the sharper arbitrarily small loss. -/
theorem eventually_projected_coefficients
    {N H : ℕ → ℝ} (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : ∀ k, 1 ≤ H k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε)
    {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ k in atTop, ∀ (G : MvPolynomial (Fin 2) ℝ) (u v β : ℝ),
      G.totalDegree ≤ 2 → |u| + |v| ≤ H k → 0 < β →
      N k ^ (-B) / H k ≤ β →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (-1 : ℝ) 1,
        |eval ![t, u + t * v + β * z] G| ≤ H k) →
      ∀ e, |G.coeff e| ≤ N k ^ (1 + 5 * B) :=
  eventually_projected_coefficients_with_loss hN hNt hH hsub hB (by norm_num)

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
