import Submission.Obl.k4_profile_density_bounds.Asymptotics
import Submission.Obl.k4_real_conic_restoration.Coordinates

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction

open Filter

/-- The Boolean tests of one parent and one scalar child fit in a common
fixed polynomial budget. -/
theorem recovery_format_bound {N : ℝ} (hN : 2 ≤ N) (M Q : ℕ) :
    N ^ M + N ^ Q ≤ N ^ (2 * M + Q + 10) := by
  have hN1 : 1 ≤ N := by linarith
  calc
    _ ≤ 2 * N ^ (M + Q) := by
      have h₁ := pow_le_pow_right₀ hN1 (show M ≤ M + Q by omega)
      have h₂ := pow_le_pow_right₀ hN1 (show Q ≤ M + Q by omega)
      linarith
    _ ≤ N ^ (M + Q + 1) := by
      rw [pow_succ]
      nlinarith [pow_nonneg (show 0 ≤ N by linarith) (M + Q)]
    _ ≤ _ := pow_le_pow_right₀ hN1 (by omega)

/-- Returning a degree-two predictor to original coordinates has fixed
polynomial coefficient complexity, even with Q0's tolerance fixed at one. -/
theorem recovery_coefficient_bound {N : ℝ} (hN : 2 ≤ N) (M Q : ℕ) :
    81 * N ^ M + 144 * N * (N ^ M) ^ 2 ≤ N ^ (2 * M + Q + 10) := by
  have hN1 : 1 ≤ N := by linarith
  have hNm : 1 ≤ N ^ M := one_le_pow₀ hN1
  have hW : N ^ M ≤ N * (N ^ M) ^ 2 := by nlinarith
  calc
    _ ≤ 225 * (N * (N ^ M) ^ 2) := by nlinarith
    _ = 225 * N ^ (2 * M + 1) := by
      rw [show 2 * M + 1 = M * 2 + 1 by omega, pow_succ N (M * 2), pow_mul N M 2]
      ring
    _ ≤ N ^ (2 * M + 1 + 8) :=
      Submission.Obl.k4_real_conic_restoration.absorb_constant hN (by norm_num)
    _ ≤ _ := pow_le_pow_right₀ hN1 (by omega)

/-- The common light-packet loss and the factor two in scalar recovery are
absorbed after selecting the original sample, without changing a format. -/
theorem eventually_recovery_mass_gap {N : ℕ → ℝ} (hN : Tendsto N atTop atTop)
    {loss η ε : ℝ} (hη : loss < η) (hε : loss < ε) :
    ∀ᶠ k in atTop, 2 * N k ^ (-ε) + N k ^ (-η) ≤ N k ^ (-loss) := by
  have h₁ := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hN (show -ε < -loss by linarith) (4 : ℝ)
  have h₂ := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hN (show -η < -loss by linarith) (2 : ℝ)
  filter_upwards [h₁, h₂] with k hk₁ hk₂
  linarith

/-- The finite light-packet threshold can be cancelled in ENNReal; no
finiteness of the recovered mass is required. -/
theorem recovery_mass_lower {a b θ : ℝ} {S : ENNReal}
    (hb : 0 ≤ b) (hθ : 0 ≤ θ) (hgap : 2 * b + θ ≤ a)
    (hrec : ENNReal.ofReal a ≤ 2 * S + ENNReal.ofReal θ) : ENNReal.ofReal b ≤ S := by
  have hnum : 2 * ENNReal.ofReal b + ENNReal.ofReal θ ≤
      2 * S + ENNReal.ofReal θ := by
    calc
      _ = ENNReal.ofReal (2 * b + θ) := by
        rw [ENNReal.ofReal_add (by positivity) hθ, ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ ≤ ENNReal.ofReal a := ENNReal.ofReal_le_ofReal hgap
      _ ≤ _ := hrec
  have htwice : 2 * ENNReal.ofReal b ≤ 2 * S :=
    (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hnum
  have heq : ENNReal.ofReal (1 / 2 : ℝ) * (2 : ENNReal) = 1 := by
    calc
      _ = ENNReal.ofReal ((1 / 2 : ℝ) * 2) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ = 1 := by norm_num
  calc
    ENNReal.ofReal b = ENNReal.ofReal (1 / 2 : ℝ) * (2 * ENNReal.ofReal b) := by
      rw [← mul_assoc, heq, one_mul]
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) * (2 * S) :=
      mul_le_mul_of_nonneg_left htwice zero_le
    _ = S := by rw [← mul_assoc, heq, one_mul]

end Submission.Obl.k4_unbounded_geometric_packet_reduction
