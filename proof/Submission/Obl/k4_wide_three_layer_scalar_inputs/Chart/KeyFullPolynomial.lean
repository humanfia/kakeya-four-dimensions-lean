/- Adapted from this LOT tree o218, branch x0950, commit 5227dd4c,
Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/KeyFullPolynomial.lean. Original attribution, when present, is preserved below. -/

import Submission.Obl.k4_wide_three_layer_scalar_inputs.Chart.KeyFrameCoordinates

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs
namespace KeyFrame

open Set MvPolynomial Submission.Obl.k4_fixed_budget_quadratic_recovery
noncomputable section

/-- The ENTIRE normalized key polynomial after following the original key
motion, written in normalized time and true transverse coordinate. -/
def chartPolynomial (F : CellFrame) (Zk Vk Yk : ℝ) (r : Fin 6 → ℝ) : Fin 6 → ℝ :=
  let b₀ := chartBeta F Zk Vk Yk 0
  let b₁ := chartBeta F Zk Vk Yk 1
  ![r 0 + r 2 * b₀ + r 5 * b₀ ^ 2,
    r 1 + r 2 * b₁ + r 4 * b₀ + 2 * r 5 * b₀ * b₁,
    r 2 / 2 + r 5 * b₀,
    r 3 + r 4 * b₁ + r 5 * b₁ ^ 2,
    r 4 / 2 + r 5 * b₁, r 5 / 4]

theorem chartPolynomial_value (F : CellFrame) (Zk Vk Yk : ℝ)
    (r : Fin 6 → ℝ) (τ U : ℝ) :
    quadraticValue (chartPolynomial F Zk Vk Yk r) τ U =
      quadraticValue r τ (chartBeta F Zk Vk Yk 0 + τ * chartBeta F Zk Vk Yk 1 + U / 2) := by
  simp [chartPolynomial, quadraticValue]
  ring

/-- Every coefficient of the whole key polynomial is subpower when the
original discrepancy coefficients and the occupied-key beta bounds are. -/
theorem chartPolynomial_bound (F : CellFrame) {Zk Vk Yk H B : ℝ}
    (hH : 0 ≤ H) (hB : 0 ≤ B)
    (hβ : |chartBeta F Zk Vk Yk 0| + |chartBeta F Zk Vk Yk 1| ≤ B)
    (r : Fin 6 → ℝ) (hr : ∀ i, |r i| ≤ H) :
    ∀ i, |chartPolynomial F Zk Vk Yk r i| ≤ 48 * H * (B + 1) ^ 2 := by
  have hnorm : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ U ∈ Icc (-1 : ℝ) 1,
      |quadraticValue (chartPolynomial F Zk Vk Yk r) τ U| ≤ 6 * H * (B + 1) ^ 2 := by
    intro τ hτ U hU
    rw [chartPolynomial_value]
    have ht : |τ| ≤ 1 := abs_le.mpr ⟨by linarith [hτ.1], hτ.2⟩
    have hu : |U| ≤ 1 := abs_le.mpr hU
    apply quadraticValue_bound hH (by linarith : 1 ≤ B + 1) hr (ht.trans (by linarith))
    calc
      _ ≤ |chartBeta F Zk Vk Yk 0 + τ * chartBeta F Zk Vk Yk 1| + |U / 2| := abs_add_le _ _
      _ ≤ |chartBeta F Zk Vk Yk 0| + |τ| * |chartBeta F Zk Vk Yk 1| + |U| / 2 := by
        have htri := add_le_add (abs_add_le (chartBeta F Zk Vk Yk 0)
          (τ * chartBeta F Zk Vk Yk 1)) (le_refl |U / 2|)
        simpa only [abs_mul, abs_div, abs_of_pos (by norm_num : 0 < (2 : ℝ))] using htri
      _ ≤ |chartBeta F Zk Vk Yk 0| + |chartBeta F Zk Vk Yk 1| + 1 / 2 := by
        have hprod : |τ| * |chartBeta F Zk Vk Yk 1| ≤ |chartBeta F Zk Vk Yk 1| := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right ht
            (abs_nonneg (chartBeta F Zk Vk Yk 1))
        linarith [div_le_div_of_nonneg_right hu (by norm_num : 0 ≤ (2 : ℝ))]
      _ ≤ _ := by linarith
  intro i
  convert quadratic_coefficients_bound hnorm i using 1 <;> ring

/-- On the key motion this whole bounded polynomial is EXACTLY the original
normalized projected residual, including its constant and time-only terms. -/
theorem chartPolynomial_residual (F : CellFrame) (hq : F.q ≠ 0) (hg : F.g ≠ 0)
    (G : MvPolynomial (Fin 2) ℝ) (r : Fin 6 → ℝ) (Zk Vk Yk : ℝ)
    (hkey : ∀ τ y : ℝ,
      (eval ![F.t₀ + F.q * τ, keyY (F.q * F.g) F.q Yk Zk τ y] G -
        F.fit (F.t₀ + F.q * τ) (keyZ Zk Vk (F.t₀ + F.q * τ))
          (keyY (F.q * F.g) F.q Yk Zk τ y)) / F.a = quadraticValue r τ y)
    (τ U : ℝ) :
    let t := F.t₀ + F.q * τ
    let Z := keyZ Zk Vk t
    let Y := baseY F t Z
    F.resid t Z (Y + F.q * F.g * U) (eval ![t, Y + F.q * F.g * U] G) =
      quadraticValue (chartPolynomial F Zk Vk Yk r) τ U := by
  rw [chartPolynomial_value]
  rw [← beta_chart F hq hg]
  have h := hkey τ (beta F Zk Yk (F.t₀ + F.q * τ)
    (keyZ Zk Vk (F.t₀ + F.q * τ)) + U / 2)
  rw [keyY_beta F hq hg] at h
  exact h

end
end KeyFrame
end Submission.Obl.k4_wide_three_layer_scalar_inputs
