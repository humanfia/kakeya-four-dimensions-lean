import Submission.Obl.k4_quadratic_finite_greedy_cover.ScaleTransfer
import Submission.Obl.k4_finite_positive_mixed_cover_realization.Interface

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

/-- One fixed constant and two incoming path factors use three small powers. -/
lemma strip_small_factor {N κ ζ C : ℝ} (hN : 0 < N) (hκ : 0 ≤ κ)
    (hκN : κ ≤ N ^ ζ) (hconst : 1242 ≤ N ^ ζ) (hC : C ≤ 1242 * κ ^ 2) :
    C ≤ N ^ (3 * ζ) := by
  calc
    C ≤ 1242 * κ ^ 2 := hC
    _ ≤ N ^ ζ * (N ^ ζ) ^ 2 := mul_le_mul hconst
      (pow_le_pow_left₀ hκ hκN 2) (sq_nonneg _) (by positivity)
    _ = N ^ (3 * ζ) := by
      rw [pow_two, ← mul_assoc, ← Real.rpow_add hN, ← Real.rpow_add hN]
      congr 1
      ring

lemma strip_factor_times_power {N C ζ x y : ℝ} (hN : 1 ≤ N)
    (hC : C ≤ N ^ ζ) (hxy : ζ + x ≤ y) : C * N ^ x ≤ N ^ y := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  calc
    _ ≤ N ^ ζ * N ^ x := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = N ^ (ζ + x) := (Real.rpow_add hN0 _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN hxy

/-- Scalar geometric hypotheses needed by the actual-label strip construction. -/
structure StripEstimates (N κ b h L ℓ ρ ε : ℝ) : Prop where
  deep : 2 * κ * N ^ (-ℓ * h * L / 4) ≤ N ^ (-b * h * L)
  candidate : N ^ (4 * ρ * h * L + 4 * ε) * N ^ (-h * L) ≤ N ^ (-b * h * L)
  small : 4 * N ^ (-b * h * L) ≤ N ^ (-b * h * L / 8)
  scale : κ * (32 * (1 + 2 * κ) * N ^ (-b * h * L) /
      N ^ (-b * h * L / 8)) ≤ δ N (b * h * L / 4)
  factor : κ * (5 + 6 * κ) * N ^ (-b * h * L / 8) ≤ N ^ (-(b * h * L / 16))

/-- All geometric losses are uniform over the actual gain once its smallest
possible product `b*h*L` dominates the fixed small exponent. -/
theorem strip_power_estimates {N κ b h L ℓ ρ ε ζ : ℝ}
    (hN : 1 ≤ N) (hκ : 1 ≤ κ) (hκN : κ ≤ N ^ ζ)
    (hconst : 1242 ≤ N ^ ζ) (hζ : 0 ≤ ζ)
    (hb : 0 ≤ b) (hb4 : b ≤ 1 / 4) (hbℓ : 8 * b ≤ ℓ)
    (hhL : 0 ≤ h * L) (hρ : ρ ≤ 1 / 16) (hε : ε ≤ ζ)
    (hmargin : 64 * ζ ≤ b * h * L) : StripEstimates N κ b h L ℓ ρ ε := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hκ0 : 0 ≤ κ := by linarith
  have hK := strip_small_factor hN0 hκ0 hκN hconst (le_rfl : 1242 * κ ^ 2 ≤ _)
  have htwo : 2 * κ ≤ N ^ (3 * ζ) := by
    apply le_trans _ hK
    nlinarith
  have hfour : (4 : ℝ) ≤ N ^ (3 * ζ) := by
    apply le_trans _ hK
    nlinarith
  have hscale : κ * (32 * (1 + 2 * κ)) ≤ N ^ (3 * ζ) := by
    apply le_trans _ hK
    nlinarith
  have hfactor : κ * (5 + 6 * κ) ≤ N ^ (3 * ζ) := by
    apply le_trans _ hK
    nlinarith
  have hbh : b * h * L = b * (h * L) := by ring
  have hℓh := mul_le_mul_of_nonneg_right hbℓ hhL
  have hbh4 := mul_le_mul_of_nonneg_right hb4 hhL
  have hρh := mul_le_mul_of_nonneg_right hρ hhL
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply strip_factor_times_power hN htwo
    nlinarith
  · rw [← Real.rpow_add hN0]
    apply Real.rpow_le_rpow_of_exponent_le hN
    nlinarith
  · apply strip_factor_times_power hN hfour
    linarith
  · calc
      _ = (κ * (32 * (1 + 2 * κ))) * N ^ (-b * h * L + b * h * L / 8) := by
        rw [Real.rpow_add hN0,
          show -b * h * L / 8 = -(b * h * L / 8) by ring,
          Real.rpow_neg hN0.le, div_eq_mul_inv, inv_inv]
        ring
      _ ≤ N ^ (-(b * h * L / 4)) := strip_factor_times_power hN hscale (by linarith)
      _ ≤ δ N (b * h * L / 4) := (k4_quadratic_finite_greedy_cover.δ_bounds hN0 _).1
  · exact strip_factor_times_power hN hfactor (by linarith)

/-- The angular joint-to-pure density ratio cancels the terminal exponent. -/
lemma strip_density_ratio {N fL S u ζ : ℝ} (hN : 0 < N) :
    N ^ (-fL - S * u + ζ) / N ^ (-fL - ζ) = N ^ (-S * u + 2 * ζ) := by
  rw [← Real.rpow_sub hN]
  congr 1
  ring

/-- The good misaligned pair charge has a fixed negative power, uniformly
over all smaller input tolerances. -/
theorem strip_angular_coefficient {N κ b h L S ρ ε ζ fL : ℝ}
    (hN : 1 ≤ N) (hκ : 1 ≤ κ) (hκN : κ ≤ N ^ ζ)
    (hconst : 1242 ≤ N ^ ζ) (hζ : 0 ≤ ζ)
    (hhL : 0 ≤ h * L) (hρ : ρ ≤ S * b / 128)
    (hε : ε ≤ ζ) (hmargin : 128 * ζ ≤ S * b * h * L) :
    (N ^ (-fL - S * (b * h * L / 4) + ζ) * 9 / N ^ (-fL - ζ)) *
        (κ * N ^ (4 * ρ * h * L + 4 * ε)) ≤
      N ^ (-(S * b * h * L / 8)) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hK := strip_small_factor hN0 (show 0 ≤ κ by linarith) hκN hconst
    (show 9 * κ ≤ 1242 * κ ^ 2 by nlinarith)
  have hρh := mul_le_mul_of_nonneg_right hρ hhL
  calc
    _ = (9 * κ) * N ^ ((-S * (b * h * L / 4) + 2 * ζ) +
        (4 * ρ * h * L + 4 * ε)) := by
      rw [Real.rpow_add hN0 (-S * (b * h * L / 4) + 2 * ζ) (4 * ρ * h * L + 4 * ε),
        ← strip_density_ratio (fL := fL) (S := S) (u := b * h * L / 4) (ζ := ζ) hN0]
      ring
    _ ≤ _ := strip_factor_times_power hN hK (by nlinarith)

end Submission.Obl.k4_finite_positive_mixed_cover_realization
