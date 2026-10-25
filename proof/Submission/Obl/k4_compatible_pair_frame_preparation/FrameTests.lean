import Submission.Obl.k4_compatible_pair_frame_preparation.FrameInput
import Submission.Obl.k4_compatible_pair_frame_preparation.FramePowers
import Submission.Obl.k4_compatible_pair_frame_preparation.FrameBudgets

namespace Submission.Obl.k4_compatible_pair_frame_preparation

open MeasureTheory Set MvPolynomial Construction

namespace NativeSample

variable {Nk : ℝ} {Wk : ℕ} {ωk : Fin Wk → ℝ}
    {νk : Fin Wk → Measure (ℕ × (Fin 6 → ℝ))}
    {Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {Pk : Fin Wk → MvPolynomial (Fin 4) ℝ} {Bk : Fin Wk → ℝ}
    {f : ℝ → ℝ}
    {gk : Fin Wk → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {Gk : Fin Wk → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    {L S a e u h : ℝ} {M D : ℕ} {depths : Finset ℝ} {ε : ℝ}

variable (p : NativeSample True 4 Nk Wk ωk νk Ek Pk Bk f gk Gk L S a e u h M D depths ε)

theorem output_value_factor (hN : 2 ≤ Nk) (ha : 0 < a) (he : 0 < e)
    (hκX : frameSlack p.κ ≤ Nk ^ (a + e))
    (hX : (2 : ℝ) ^ 100 ≤ Nk ^ (a + e)) :
    12 * p.toPrep.κ₀ * (2 ^ p.toPrep.s + 1) ^ 2 ≤ Nk ^ (100 * (a + e)) := by
  have hN1 : 1 ≤ Nk := by linarith
  have hN0 : 0 < Nk := by linarith
  have hq : (2 : ℝ) ^ p.s ≤ 2 * Nk ^ (a + e) :=
    p.hgainhi.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (by norm_num))
  have hX1 : 1 ≤ Nk ^ (a + e) := Real.one_le_rpow hN1 (by linarith)
  calc
    12 * p.toPrep.κ₀ * (2 ^ p.toPrep.s + 1) ^ 2 ≤ (Nk ^ (a + e)) ^ 4 :=
      coarse_value_factor_le hX (zero_le_one.trans p.κ_one)
        ((frameSlack_input p.κ_one).trans hκX) (by positivity) hq
    _ ≤ (Nk ^ (a + e)) ^ 100 := pow_le_pow_right₀ hX1 (by omega)
    _ = Nk ^ (100 * (a + e)) := by
      rw [← Real.rpow_mul_natCast hN0.le]
      congr 1
      ring

theorem output_derivative_floor (hN : 2 ≤ Nk) (ha : 0 < a) (he : 0 < e) :
    Nk ^ (-(100 * (a + e))) ≤ p.toPrep.dfl := by
  change Nk ^ (-(100 * (a + e))) ≤ Nk ^ (-a)
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

end NativeSample
end Submission.Obl.k4_compatible_pair_frame_preparation
