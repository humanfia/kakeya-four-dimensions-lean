-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.MediumCountPowers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.MediumPowers
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PowerBudgets

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

noncomputable def mediumConstant (C σ ω : ℝ) : ℝ :=
  C * 8 * ((513 : ℝ) ^ 6) ^ (1 + σ / 2) * (800000000 : ℝ) ^ ((ω + σ) / 2)

lemma mediumConstant_pos {C σ ω : ℝ} (hC : 0 < C) : 0 < mediumConstant C σ ω := by
  dsimp [mediumConstant]
  positivity

lemma grain_weight_power_lower {δ b a ρ θ s c : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hρ : 0 < ρ) (hθ : 0 < θ) (hs : 0 < s) (hc : 0 < c)
    (hconf : s * ρ * c ≤ δ ^ (-b) * a) :
    (δ ^ b / 800000000) * (ρ / θ) ^ 2 ≤ a * ρ / (800000000 * θ ^ 2 * s * c) := by
  calc
    _ = (1 / (800000000 * δ ^ (-b))) * (ρ / θ) ^ 2 := by
      rw [Real.rpow_neg hδ.le]
      field_simp
    _ ≤ _ := grain_packet_weight_lower ha hρ hθ hs hc (Real.rpow_pos_of_pos hδ _) hconf

theorem medium_count_power_bound {δ b ν h loss C σ ω a ρ b₀ s c : ℝ} {A : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (hC : 0 < C) (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 ≤ ω) (hω1 : ω ≤ 1)
    (ha : 0 < a) (hρ : 0 < ρ) (hb₀ : 0 < b₀) (hs : 0 < s) (hc : 0 < c)
    (hA : (A : ℝ) ≤ 2 * δ ^ (-b)) (hconf : s * ρ * c ≤ δ ^ (-b) * a)
    (hloss : 18 * b + ν + 2 * h ≤ loss) :
    C * (δ ^ (2 : ℕ)) ^ (-b) * (δ ^ ν / 8)⁻¹ *
      ((((128 * A ^ 2 + 1) ^ 6 : ℕ) : ℝ) * δ ^ (-h)) ^ (1 + σ / 2) *
      (a * ρ / (800000000 * (min 1 b₀) ^ 2 * s * c)) ^ (-(ω + σ) / 2) ≤
      mediumConstant C σ ω * δ ^ (-loss) * (ρ / b₀) ^ (-ω - σ) := by
  have hθ : 0 < min 1 b₀ := lt_min zero_lt_one hb₀
  have hpacket : ((((128 * A ^ 2 + 1) ^ 6 : ℕ) : ℝ) * δ ^ (-h)) ≤
      (513 : ℝ) ^ 6 * δ ^ (-(12 * b + h)) := by
    calc
      _ ≤ ((513 : ℝ) ^ 6 * δ ^ (-(12 * b))) * δ ^ (-h) :=
        mul_le_mul_of_nonneg_right (packet_count_power_bound hδ hδ1 hb hA) (Real.rpow_nonneg hδ.le _)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hδ]; congr 2; ring
  have hw := grain_weight_power_lower hδ ha hρ hθ hs hc hconf
  have hbound := medium_volume_factor_bound (e := 2 * b) (ν := ν) (χ := 12 * b + h)
    (β := b) hδ (div_pos hρ hθ) hC (by positivity : 0 < (513 : ℝ) ^ 6)
    (by norm_num : (0 : ℝ) < 800000000) (by positivity) hσ hω le_rfl hpacket hw
  have hp : (δ ^ (2 : ℕ)) ^ (-b) = δ ^ (-(2 * b)) := by rw [square_rpow hδ]; congr 1; ring
  rw [hp]
  apply hbound.trans
  have hexp := medium_loss_bound (e := b) (ν := ν) hb hh hσ hσhalf hω1
  have hδpow : δ ^ (-(2 * b + ν + (12 * b + h) * (1 + σ / 2) + b * (ω + σ) / 2)) ≤
      δ ^ (-loss) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hrpow : (ρ / min 1 b₀) ^ (-ω - σ) ≤ (ρ / b₀) ^ (-ω - σ) :=
    Real.rpow_le_rpow_of_nonpos (div_pos hρ hb₀)
      (div_le_div_of_nonneg_left hρ.le hθ (min_le_right _ _)) (by linarith)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hδpow (mediumConstant_pos hC).le)
    hrpow (Real.rpow_nonneg (div_nonneg hρ.le hθ.le) _)
    (mul_nonneg (mediumConstant_pos hC).le (Real.rpow_nonneg hδ.le _))

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
