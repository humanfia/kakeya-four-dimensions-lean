/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/DirectionalMargins.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeResolution

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Filter
open Submission.Obl.k4_critical_intercept_concentration.Data
open Submission.Obl.k4_profile_density_bounds

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Both errors in the sb=3s0/2 comparison row have a fixed positive power
saving. The matching loss can be chosen arbitrarily small below this margin. -/
theorem Prepared.eventually_fine_row_error (h : cfg.Prepared) {s₀ ε : ℝ}
    (hs₀ : 0 < s₀)
    (hε : ε ≤ s₀ * min cfg.κ (1 - 2 * cfg.κ) / 16) :
    ∀ᶠ k in atTop, ∀ a : cfg.AssignmentLevel k (3 * s₀ / 2),
      (cfg.N k ^ (-(2 * cfg.κ * s₀)) / cfg.N k ^ (-s₀)) *
        (cfg.N k ^ ε * cfg.N k ^ (-s₀) / cfg.timeLength k (3 * s₀ / 2) +
          6 * cfg.N k ^ ε * cfg.N k ^ (-(3 * s₀ / 2)) /
            cfg.N k ^ (-(2 * cfg.κ * (3 * s₀ / 2)))) ≤
        cfg.N k ^ (-(s₀ * min cfg.κ (1 - 2 * cfg.κ) / 4)) := by
  let m := min cfg.κ (1 - 2 * cfg.κ)
  have hm : 0 < m := lt_min h.rate_pos (by linarith [h.subcritical_rate])
  have hmk : m ≤ cfg.κ := min_le_left _ _
  have hmτ : m ≤ 1 - 2 * cfg.κ := min_le_right _ _
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hgap : ε - s₀ * m / 2 < -(s₀ * m / 4) := by
    change ε ≤ s₀ * m / 16 at hε
    nlinarith [mul_pos hs₀ hm]
  have hsmall := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    1 hgap (show (0 : ℝ) ≤ 7 by norm_num)
  filter_upwards [hsmall] with k hk
  intro a
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hq : 0 < cfg.timeLength k (3 * s₀ / 2) := by unfold timeLength; positivity
  have hA₀ : 0 < cfg.N k ^ (-s₀) := Real.rpow_pos_of_pos hN _
  have hDb : 0 < cfg.N k ^ (-(2 * cfg.κ * (3 * s₀ / 2))) := Real.rpow_pos_of_pos hN _
  have hqinv : (cfg.timeLength k (3 * s₀ / 2))⁻¹ ≤
      cfg.K k * cfg.N k ^ (cfg.κ * (3 * s₀ / 2)) := by
    simpa only [timeLength, inv_inv] using a.time_upper
  have hfirst :
      (cfg.N k ^ (-(2 * cfg.κ * s₀)) / cfg.N k ^ (-s₀)) *
        (cfg.N k ^ ε * cfg.N k ^ (-s₀) / cfg.timeLength k (3 * s₀ / 2)) ≤
      cfg.K k * cfg.N k ^ (ε - s₀ * m / 2) := by
    calc
      _ = (cfg.N k ^ ε * cfg.N k ^ (-(2 * cfg.κ * s₀))) *
          (cfg.timeLength k (3 * s₀ / 2))⁻¹ := by
        field_simp [hA₀.ne', hq.ne']
      _ ≤ (cfg.N k ^ ε * cfg.N k ^ (-(2 * cfg.κ * s₀))) *
          (cfg.K k * cfg.N k ^ (cfg.κ * (3 * s₀ / 2))) :=
        mul_le_mul_of_nonneg_left hqinv (by positivity)
      _ = cfg.K k * cfg.N k ^ (ε - cfg.κ * s₀ / 2) := by
        rw [show (cfg.N k ^ ε * cfg.N k ^ (-(2 * cfg.κ * s₀))) *
            (cfg.K k * cfg.N k ^ (cfg.κ * (3 * s₀ / 2))) =
            cfg.K k * ((cfg.N k ^ ε * cfg.N k ^ (-(2 * cfg.κ * s₀))) *
              cfg.N k ^ (cfg.κ * (3 * s₀ / 2))) by ring,
          ← Real.rpow_add hN, ← Real.rpow_add hN]
        congr 1
        congr 1
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hK)
        apply Real.rpow_le_rpow_of_exponent_le (hN1 k)
        nlinarith [mul_le_mul_of_nonneg_left hmk hs₀.le]
  have hsecond :
      (cfg.N k ^ (-(2 * cfg.κ * s₀)) / cfg.N k ^ (-s₀)) *
        (6 * cfg.N k ^ ε * cfg.N k ^ (-(3 * s₀ / 2)) /
          cfg.N k ^ (-(2 * cfg.κ * (3 * s₀ / 2)))) ≤
      6 * cfg.K k * cfg.N k ^ (ε - s₀ * m / 2) := by
    have heq :
        (cfg.N k ^ (-(2 * cfg.κ * s₀)) / cfg.N k ^ (-s₀)) *
          (6 * cfg.N k ^ ε * cfg.N k ^ (-(3 * s₀ / 2)) /
            cfg.N k ^ (-(2 * cfg.κ * (3 * s₀ / 2)))) =
          6 * cfg.N k ^ (ε - (1 - 2 * cfg.κ) * s₀ / 2) := by
      have hexp : ε - (1 - 2 * cfg.κ) * s₀ / 2 =
          ((ε + -(2 * cfg.κ * s₀)) + -(3 * s₀ / 2)) -
            ((-s₀) + -(2 * cfg.κ * (3 * s₀ / 2))) := by ring
      rw [hexp, Real.rpow_sub hN, Real.rpow_add hN, Real.rpow_add hN,
        Real.rpow_add hN]
      field_simp [hA₀.ne', hDb.ne']
    rw [heq]
    calc
      _ ≤ 6 * cfg.N k ^ (ε - s₀ * m / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 6)
        apply Real.rpow_le_rpow_of_exponent_le (hN1 k)
        nlinarith [mul_le_mul_of_nonneg_left hmτ hs₀.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith : 6 ≤ 6 * cfg.K k)
        (Real.rpow_nonneg hN.le _)
  rw [mul_add]
  calc
    _ ≤ cfg.K k * cfg.N k ^ (ε - s₀ * m / 2) +
        6 * cfg.K k * cfg.N k ^ (ε - s₀ * m / 2) := add_le_add hfirst hsecond
    _ = 7 * cfg.K k * cfg.N k ^ (ε - s₀ * m / 2) := by ring
    _ ≤ _ := by simpa only [pow_one] using hk.le

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
