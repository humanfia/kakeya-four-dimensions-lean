import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

/-- A common polynomial envelope for all scale-comparison coefficients. -/
def precisionEnvelope (H Hg R Q : ℝ) : ℝ :=
  10 + 10 * H + 10 * Hg + 100 * (1 + H) * R + 100 * Q ^ 2

/-- Three scalar scale gaps pay for all four geometric precision
conditions. The first row grid is stopped at the fixed coarse scale. -/
theorem precision_kernel {H Hg R Q ρ b z ζ : ℝ}
    (hH : 0 ≤ H) (hHg : 0 ≤ Hg) (hR : 0 ≤ R)
    (hρ : 0 < ρ) (hb : 0 ≤ b) (hz : 0 ≤ z) (hζ : 0 ≤ ζ)
    (hbρ : b ≤ ρ) (hzρ : z ≤ ρ)
    (heρ : precisionEnvelope H Hg R Q * ρ ≤ ζ / 10)
    (heb : precisionEnvelope H Hg R Q * b ≤ ρ * ζ / 10)
    (hez : precisionEnvelope H Hg R Q * z ≤ ρ * ζ / 10) :
    (1 + 3 * (H + 1)) * b ≤ ρ * ζ ∧
    (Hg * z + R * (ρ + 2 * b + ρ) * (1 + H)) * (ρ + 2 * b) +
      2 * (1 + 2 * Hg) * b ≤ ρ * ζ ∧
    4 * Q ^ 2 * ρ + Hg * z / ρ + 2 * (H + 1) * b / ρ ≤ ζ ∧
    2 * (R * (ρ + 2 * b + ρ) + 4 * Q ^ 2 * ρ) +
      (1 + 2 * Hg) * b / ρ ≤ ζ := by
  let D := precisionEnvelope H Hg R Q
  have hD : 0 ≤ D := by dsimp only [D, precisionEnvelope]; positivity
  have hHR : 0 ≤ (1 + H) * R := mul_nonneg (by linarith) hR
  have hpoint : 1 + 3 * (H + 1) ≤ D := by
    dsimp only [D, precisionEnvelope]
    nlinarith only [hH, hHg, hHR, sq_nonneg Q]
  have hvar : 3 * Hg + 12 * R * (1 + H) ≤ D := by
    dsimp only [D, precisionEnvelope]
    nlinarith only [hH, hHg, hHR, sq_nonneg Q]
  have hbcoef : 2 * (1 + 2 * Hg) ≤ D := by
    dsimp only [D, precisionEnvelope]
    nlinarith only [hH, hHg, hHR, sq_nonneg Q]
  have hQ : 4 * Q ^ 2 ≤ D := by
    dsimp only [D, precisionEnvelope]
    nlinarith only [hH, hHg, hHR, sq_nonneg Q]
  have hG : Hg ≤ D := by
    dsimp only [D, precisionEnvelope]
    nlinarith only [hH, hHg, hHR, sq_nonneg Q]
  have hHcoef : 2 * (H + 1) ≤ D := by
    dsimp only [D, precisionEnvelope]
    nlinarith only [hH, hHg, hHR, sq_nonneg Q]
  have hscoef : 8 * R + 8 * Q ^ 2 ≤ D := by
    have hm : R ≤ (1 + H) * R := by nlinarith only [mul_nonneg hH hR]
    dsimp only [D, precisionEnvelope]
    nlinarith only [hH, hHg, hHR, sq_nonneg Q, hm]
  have hsbin : 1 + 2 * Hg ≤ D := by linarith only [hbcoef, hHg]
  have hbratio : D * b / ρ ≤ ζ / 10 :=
    (div_le_iff₀ hρ).mpr (by dsimp only [D]; nlinarith only [heb])
  have hzratio : D * z / ρ ≤ ζ / 10 :=
    (div_le_iff₀ hρ).mpr (by dsimp only [D]; nlinarith only [hez])
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right hpoint hb).trans
      (heb.trans (by nlinarith only [mul_nonneg hρ.le hζ]))
  · have hlarge :
        (Hg * z + R * (ρ + 2 * b + ρ) * (1 + H)) * (ρ + 2 * b) +
          2 * (1 + 2 * Hg) * b ≤
        (3 * Hg + 12 * R * (1 + H)) * ρ ^ 2 + 2 * (1 + 2 * Hg) * b := by
      calc
        _ ≤ (Hg * ρ + R * (4 * ρ) * (1 + H)) * (3 * ρ) +
              2 * (1 + 2 * Hg) * b := by gcongr <;> linarith
        _ = _ := by ring
    have henvelope := hlarge.trans (add_le_add
      (mul_le_mul_of_nonneg_right hvar (sq_nonneg ρ))
      (mul_le_mul_of_nonneg_right hbcoef hb))
    have hρcost := mul_le_mul_of_nonneg_right heρ hρ.le
    change D * ρ * ρ ≤ ζ / 10 * ρ at hρcost
    change D * b ≤ ρ * ζ / 10 at heb
    nlinarith only [henvelope, hρcost, heb, mul_nonneg hρ.le hζ]
  · calc
      _ ≤ D * ρ + D * z / ρ + D * b / ρ := by
        gcongr
      _ ≤ ζ / 10 + ζ / 10 + ζ / 10 :=
        add_le_add (add_le_add heρ hzratio) hbratio
      _ ≤ ζ := by linarith
  · have hlarge :
        2 * (R * (ρ + 2 * b + ρ) + 4 * Q ^ 2 * ρ) +
          (1 + 2 * Hg) * b / ρ ≤
        (8 * R + 8 * Q ^ 2) * ρ + (1 + 2 * Hg) * b / ρ := by
      have hh : ρ + 2 * b + ρ ≤ 4 * ρ := by linarith
      nlinarith only [mul_le_mul_of_nonneg_left hh hR]
    calc
      _ ≤ (8 * R + 8 * Q ^ 2) * ρ + (1 + 2 * Hg) * b / ρ := hlarge
      _ ≤ D * ρ + D * b / ρ := by gcongr
      _ ≤ ζ / 10 + ζ / 10 := add_le_add heρ hbratio
      _ ≤ ζ := by linarith

end Submission.Obl.k4_scalar_graph_residual_discovery

namespace Submission.Obl.k4_scalar_graph_residual_discovery

/-- The scale-comparison envelope uses only a fixed polynomial in the
original bound and two powers of the first-grid ratio. -/
theorem precisionEnvelope_le {H Hg R Q U X : ℝ}
    (hU : 1 ≤ U) (hH : 0 ≤ H) (hHU : H ≤ U) (hHg : 0 ≤ Hg) (hHgU : Hg ≤ U)
    (hR : 0 ≤ R) (hRX : R ≤ 102 * U ^ 2 * X)
    (hQ : 0 ≤ Q) (hQX : Q ≤ 128 * U ^ 2 * X) (hX : 1 ≤ X) :
    precisionEnvelope H Hg R Q ≤ 2000000 * U ^ 4 * X ^ 2 := by
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hU2 : 1 ≤ U ^ 2 := one_le_pow₀ hU
  have hU3 : 1 ≤ U ^ 3 := one_le_pow₀ hU
  have hX2 : 1 ≤ X ^ 2 := one_le_pow₀ hX
  have hUX : U ^ 3 * X ≤ U ^ 4 * X ^ 2 := by
    calc
      _ ≤ U ^ 4 * X := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hU (by norm_num : 3 ≤ 4)) hX0
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith only [hX, mul_nonneg hX0 (sub_nonneg.mpr hX)]) (pow_nonneg hU0 4)
  have hUfour : U ≤ U ^ 4 * X ^ 2 := by
    calc
      _ ≤ U ^ 4 := by simpa only [pow_one] using (pow_le_pow_right₀ hU (by norm_num : 1 ≤ 4))
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hX2 (pow_nonneg hU0 4)
  have hfirst : 10 + 10 * H + 10 * Hg ≤ 30 * U := by linarith
  have hmiddle : 100 * (1 + H) * R ≤ 20400 * (U ^ 4 * X ^ 2) := by
    calc
      _ ≤ 100 * (2 * U) * (102 * U ^ 2 * X) := by gcongr <;> linarith
      _ = 20400 * (U ^ 3 * X) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hUX (by norm_num)
  have hlast : 100 * Q ^ 2 ≤ 1638400 * (U ^ 4 * X ^ 2) := by
    calc
      _ ≤ 100 * (128 * U ^ 2 * X) ^ 2 := by gcongr
      _ = _ := by ring
  have hbase := mul_le_mul_of_nonneg_left hUfour (by norm_num : (0 : ℝ) ≤ 30)
  dsimp only [precisionEnvelope]
  nlinarith only [hfirst, hmiddle, hlast, hbase, mul_nonneg (pow_nonneg hU0 4) (sq_nonneg X)]

end Submission.Obl.k4_scalar_graph_residual_discovery
