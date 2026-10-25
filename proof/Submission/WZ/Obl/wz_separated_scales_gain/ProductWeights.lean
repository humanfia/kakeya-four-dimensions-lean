-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_scales_gain.ProductWeights.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_scales_gain.Scalar

namespace WangZahlLot.Obl.wz_separated_scales_gain

/-- The three cardinality weights telescope to the original cardinality and saturation. -/
theorem tower_weight_identity {N M Q δ τ ρ : ℝ} (hN : 0 < N) (hM : 0 < M)
    (hQ : 0 < Q) (hδ : 0 < δ) (hτ : 0 < τ) (hρ : 0 < ρ) (σ : ℝ) :
    (N * (δ / τ) ^ 4) ^ (σ / 2) *
      ((M * (τ / ρ) ^ 2) * (M * (τ / ρ)) ^ (-σ)) *
      (Q * ρ ^ 4) ^ (σ / 2) =
    (N * M * Q * δ ^ 4) ^ (σ / 2) * (M * (τ / ρ) ^ 2) ^ (1 - 3 * σ / 2) := by
  apply Real.log_injOn_pos (by change (0 : ℝ) < _; positivity) (by change (0 : ℝ) < _; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow, Real.log_rpow]
  ring

/-- The scale powers telescope, leaving exactly the exponent difference between `E` and `D`. -/
theorem tower_scale_identity {δ τ ρ : ℝ} (hδ : 0 < δ) (hτ : 0 < τ) (hρ : 0 < ρ)
    (u ω e : ℝ) :
    (δ / τ) ^ (u + e) * (τ / ρ) ^ (ω + e) * ρ ^ (u + e) =
      δ ^ (u + e) * (ρ / τ) ^ (u - ω) := by
  apply Real.log_injOn_pos (by change (0 : ℝ) < _; positivity) (by change (0 : ℝ) < _; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
  ring

/-- Balance and middle saturation lose at most two powers of the structural constant. -/
theorem tower_weight_lower {N M Q n δ τ ρ L σ : ℝ}
    (hN : 0 < N) (hM : 0 < M) (hQ : 0 < Q) (hn : 0 ≤ n)
    (hδ : 0 < δ) (hτ : 0 < τ) (hρ : 0 < ρ) (hL : 1 ≤ L)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2)
    (hcard : n ≤ L ^ 2 * (N * M * Q)) (hsat : L⁻¹ ≤ M * (τ / ρ) ^ 2) :
    L⁻¹ ^ 2 * (n * δ ^ 4) ^ (σ / 2) ≤
      (N * (δ / τ) ^ 4) ^ (σ / 2) *
        ((M * (τ / ρ) ^ 2) * (M * (τ / ρ)) ^ (-σ)) * (Q * ρ ^ 4) ^ (σ / 2) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hpowL : (L ^ 2) ^ (σ / 2) ≤ L := by
    rw [← Real.rpow_natCast L 2, ← Real.rpow_mul hL0.le]
    have he : (2 : ℝ) * (σ / 2) ≤ 1 := by linarith
    exact (Real.rpow_le_rpow_of_exponent_le hL he).trans_eq (Real.rpow_one L)
  have hcard' : L⁻¹ * (n * δ ^ 4) ^ (σ / 2) ≤ (N * M * Q * δ ^ 4) ^ (σ / 2) := by
    have hh : (n * δ ^ 4) ^ (σ / 2) ≤ L * (N * M * Q * δ ^ 4) ^ (σ / 2) := by
      calc
        _ ≤ (L ^ 2 * (N * M * Q * δ ^ 4)) ^ (σ / 2) := by
          apply Real.rpow_le_rpow (by positivity) _ (by positivity)
          nlinarith [mul_le_mul_of_nonneg_right hcard (pow_nonneg hδ.le 4)]
        _ = (L ^ 2) ^ (σ / 2) * (N * M * Q * δ ^ 4) ^ (σ / 2) :=
          Real.mul_rpow (by positivity) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right hpowL (by positivity)
    exact (inv_mul_le_iff₀ hL0).mpr hh
  have hsat' : L⁻¹ ≤ (M * (τ / ρ) ^ 2) ^ (1 - 3 * σ / 2) := by
    calc
      _ ≤ (L⁻¹) ^ (1 - 3 * σ / 2) :=
        Real.self_le_rpow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hL) (by linarith)
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hsat (by linarith)
  rw [tower_weight_identity hN hM hQ hδ hτ hρ]
  have hh := mul_le_mul hcard' hsat' (by positivity) (by positivity)
  convert hh using 1 <;> ring

end WangZahlLot.Obl.wz_separated_scales_gain
