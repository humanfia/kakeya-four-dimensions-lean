import Submission.Obl.k4_horizon_chart_assembly.Envelope

namespace Submission.Obl.k4_horizon_chart_assembly

noncomputable section

def atlasSize (H K τ₀ : ℝ) (D T : ℕ) : ℝ :=
  1 + H + K + (D : ℝ) + (2 : ℝ) ^ T + τ₀⁻¹

/-- One fixed universal exponent absorbs every per-group chart budget and the
unweighted count of the full world/block/group/plank family. -/
theorem global_atlas_budget {H K τ₀ : ℝ} {D T W : ℕ}
    (hH : 2 ≤ H) (hK : 1 ≤ K) (hτ : 0 < τ₀) (hW : (W : ℝ) ≤ H) :
    packetEnvelope H K (2 * K + 2) (((2 : ℝ) ^ T)⁻¹) τ₀ D ≤ atlasSize H K τ₀ D T ^ 16 ∧
    (D : ℝ) ^ 2 / (4 * τ₀) * (W : ℝ) * (2 : ℝ) ^ T ≤ atlasSize H K τ₀ D T ^ 16 := by
  let V := atlasSize H K τ₀ D T
  have hH₀ : 0 ≤ H := by linarith
  have hK₀ : 0 ≤ K := by linarith
  have hτinv : 0 < τ₀⁻¹ := inv_pos.mpr hτ
  have hD₀ : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hJ₀ : 0 ≤ (2 : ℝ) ^ T := by positivity
  have hV4 : 4 ≤ V := by dsimp [V, atlasSize]; linarith
  have hV1 : 1 ≤ V := by linarith
  have hV₀ : 0 ≤ V := by linarith
  have hHV : H ≤ V := by dsimp [V, atlasSize]; linarith
  have hKV : K + 1 ≤ V := by dsimp [V, atlasSize]; linarith
  have hDV : (D : ℝ) ≤ V := by dsimp [V, atlasSize]; linarith
  have hJV : (2 : ℝ) ^ T ≤ V := by dsimp [V, atlasSize]; linarith
  have hτV : τ₀⁻¹ ≤ V := by dsimp [V, atlasSize]; linarith
  have hWV : (W : ℝ) ≤ V := hW.trans hHV
  have hsize : packetSize H K (2 * K + 2) (((2 : ℝ) ^ T)⁻¹) τ₀ D ≤ 3 * V := by
    dsimp [packetSize, V, atlasSize]
    rw [inv_inv]
    linarith
  have hsize₀ : 0 ≤ packetSize H K (2 * K + 2) (((2 : ℝ) ^ T)⁻¹) τ₀ D := by
    dsimp [packetSize]
    positivity
  have hconst : (82944 : ℝ) ≤ V ^ 12 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hV4 12
    norm_num at hp
    linarith
  constructor
  · change 1024 * _ ^ 4 ≤ V ^ 16
    calc
      _ ≤ 1024 * (3 * V) ^ 4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsize₀ hsize 4) (by norm_num)
      _ = 82944 * V ^ 4 := by ring
      _ ≤ V ^ 12 * V ^ 4 := mul_le_mul_of_nonneg_right hconst (pow_nonneg hV₀ 4)
      _ = _ := by ring
  · have hA : (D : ℝ) ^ 2 / (4 * τ₀) ≤ V ^ 3 := by
      calc
        _ = ((D : ℝ) ^ 2 * τ₀⁻¹) / 4 := by ring
        _ ≤ (D : ℝ) ^ 2 * τ₀⁻¹ := by
          nlinarith [mul_nonneg (sq_nonneg (D : ℝ)) hτinv.le]
        _ ≤ V ^ 2 * V := mul_le_mul (pow_le_pow_left₀ hD₀ hDV 2) hτV hτinv.le (sq_nonneg V)
        _ = _ := by ring
    change _ ≤ V ^ 16
    calc
      _ ≤ (V ^ 3 * V) * V := mul_le_mul
        (mul_le_mul hA hWV (Nat.cast_nonneg _) (pow_nonneg hV₀ 3)) hJV hJ₀
        (mul_nonneg (pow_nonneg hV₀ 3) hV₀)
      _ = V ^ 5 := by ring
      _ ≤ _ := pow_le_pow_right₀ hV1 (by omega)

end
end Submission.Obl.k4_horizon_chart_assembly
