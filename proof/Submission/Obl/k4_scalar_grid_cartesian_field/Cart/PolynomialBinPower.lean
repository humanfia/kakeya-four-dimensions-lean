-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/PolynomialBinPower.lean;
-- only the namespace was renamed into o230's.
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.PolynomialBinSampling

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

theorem polynomial_bin_count_power_bound (D : ℕ) (C K : ℝ)
    (hC : 0 ≤ C) (hK : 1 ≤ K) :
    (2 / (K⁻¹)^(D+1)) * K^(D+1) *
      (7 + 4 * C * K * (((D : ℝ) + 1) *
        (8 * ((D : ℝ) + 1)^2 / (K⁻¹)^(D+1))^D))^(D+1) ≤
    (2 * (7 + 4 * C * ((D : ℝ) + 1) * (8 * ((D : ℝ) + 1)^2)^D)^(D+1)) *
      K^(3 * (D+1) + (D+1)^2 * D) := by
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  let W := 7 + 4 * C * ((D : ℝ) + 1) * (8 * ((D : ℝ) + 1)^2)^D
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hpow : 1 ≤ K^(1 + (D+1)*D) := one_le_pow₀ hK
  have hinner : 7 + 4 * C * K * (((D : ℝ) + 1) *
      (8 * ((D : ℝ) + 1)^2 / (K⁻¹)^(D+1))^D) ≤
      W * K^(1 + (D+1)*D) := by
    have heq : 4 * C * K * (((D : ℝ) + 1) *
        (8 * ((D : ℝ) + 1)^2 / (K⁻¹)^(D+1))^D) =
        (4 * C * ((D : ℝ) + 1) * (8 * ((D : ℝ) + 1)^2)^D) *
          K^(1 + (D+1)*D) := by
      rw [inv_pow, div_inv_eq_mul, mul_pow, ← pow_mul, pow_add, pow_one]
      ring
    rw [heq]
    dsimp [W]
    nlinarith only [hpow]
  change (2 / (K⁻¹)^(D+1)) * K^(D+1) *
      (7 + 4 * C * K * (((D : ℝ) + 1) *
        (8 * ((D : ℝ) + 1)^2 / (K⁻¹)^(D+1))^D))^(D+1) ≤
    (2 * W^(D+1)) * K^(3 * (D+1) + (D+1)^2 * D)
  calc
    _ ≤ (2 / (K⁻¹)^(D+1)) * K^(D+1) *
        (W * K^(1 + (D+1)*D))^(D+1) := by
      apply mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hinner (D+1))
      positivity
    _ = _ := by
      simp only [inv_pow, div_inv_eq_mul, mul_pow, ← pow_mul]
      ring_nf

/-- Polynomial-bin complexity is subpower whenever the original row
length, field list and fitting losses are subpower. The degree fixes
the displayed power before any asymptotic tolerance is chosen. -/
theorem exists_original_polynomial_bin_power_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K ε : ℝ), 1 ≤ K → 0 < ε →
      ∀ (S : Finset (Fin (D + 1) → ℤ)) (p : (Fin (D + 1) → ℤ) → Polynomial ℝ),
      (∀ c ∈ S, (p c).natDegree ≤ D) →
      (∀ c ∈ S, ∀ k : Fin (D + 1), ⌊(p c).coeff k / ε⌋ = c k) →
      ∀ (A : (Fin (D + 1) → ℤ) → Set ℝ),
      (∀ c ∈ S, MeasurableSet (A c)) →
      (∀ c ∈ S, A c ⊆ Set.Icc (0 : ℝ) 1) →
      (∀ c ∈ S, ENNReal.ofReal K⁻¹ ≤ MeasureTheory.volume (A c)) →
      ∀ (L : ℝ → Finset ℤ),
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ((L t).card : ℝ) ≤ K) →
      (∀ c ∈ S, ∀ t ∈ A c, ∃ z ∈ L t,
        |(p c).eval t - ε * (z : ℝ)| ≤ K * ε) →
      (S.card : ℝ) ≤ C * K^(3 * (D+1) + (D+1)^2 * D) := by
  obtain ⟨C, hC, hcount⟩ := exists_polynomial_floor_bin_count_constant D
  let W := 7 + 4 * C * ((D : ℝ) + 1) * (8 * ((D : ℝ) + 1)^2)^D
  have hW : 0 < W := by dsimp [W]; positivity
  refine ⟨2 * W^(D+1), by positivity, ?_⟩
  intro K ε hK hε S p hp hcode A hAm hAunit hAlength L hL hfit
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have h := hcount K⁻¹ K ε K (inv_pos.mpr hK0) hK0.le hε hK0.le
    S p hp hcode A hAm hAunit hAlength L hL hfit
  exact h.trans (polynomial_bin_count_power_bound D C K hC.le hK)

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
