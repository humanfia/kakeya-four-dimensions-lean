/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/TerminalErrors.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeResolution

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Filter
open Submission.Obl.k4_critical_intercept_concentration.Data
open Submission.Obl.k4_profile_density_bounds

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

theorem Prepared.eventually_terminal_collapse_error (h : cfg.Prepared) {s₀ s η : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s)
    (hnear : s - s₀ ≤ s₀ * min cfg.κ (1 - 2 * cfg.κ) / 16)
    (hη : η ≤ s₀ * min cfg.κ (1 - 2 * cfg.κ) / 16) :
    ∀ᶠ k in atTop, ∀ a : cfg.AssignmentLevel k s,
      cfg.N k ^ η * cfg.N k ^ (-(2 * cfg.κ * s₀)) / cfg.timeLength k s +
        cfg.N k ^ (-(s₀ * min cfg.κ (1 - 2 * cfg.κ) / 4)) ≤
          cfg.N k ^ (-(s - s₀)) := by
  let m := min cfg.κ (1 - 2 * cfg.κ)
  let g := s₀ * m / 8
  have hm : 0 < m := lt_min h.rate_pos (by linarith [h.subcritical_rate])
  have hg : 0 < g := by dsimp [g]; positivity
  have hmk : m ≤ cfg.κ := min_le_left _ _
  have hdelta : 0 ≤ s - s₀ := sub_nonneg.mpr hs
  have hkdelta := mul_le_mul_of_nonneg_right h.rate_le_one hdelta
  have hmκ := mul_le_mul_of_nonneg_left hmk hs₀.le
  have hfirstexp : η - 2 * cfg.κ * s₀ + cfg.κ * s ≤ -(s - s₀) - g := by
    dsimp [g]
    change s - s₀ ≤ s₀ * m / 16 at hnear
    change η ≤ s₀ * m / 16 at hη
    nlinarith [mul_pos hs₀ hm]
  have hsecondexp : -(s₀ * m / 4) ≤ -(s - s₀) - g := by
    dsimp [g]
    change s - s₀ ≤ s₀ * m / 16 at hnear
    nlinarith [mul_pos hs₀ hm]
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hsmall := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    1 (show -(s - s₀) - g < -(s - s₀) by linarith) (show (0 : ℝ) ≤ 2 by norm_num)
  filter_upwards [hsmall] with k hk
  intro a
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hK0 : 0 ≤ cfg.K k := zero_le_one.trans hK
  have hi : (cfg.timeLength k s)⁻¹ ≤ cfg.K k * cfg.N k ^ (cfg.κ * s) := by
    simpa only [timeLength, inv_inv] using a.time_upper
  have hfirst : cfg.N k ^ η * cfg.N k ^ (-(2 * cfg.κ * s₀)) / cfg.timeLength k s ≤
      cfg.K k * cfg.N k ^ (-(s - s₀) - g) := by
    calc
      _ ≤ (cfg.N k ^ η * cfg.N k ^ (-(2 * cfg.κ * s₀))) *
          (cfg.K k * cfg.N k ^ (cfg.κ * s)) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hi (by positivity)
      _ = cfg.K k * cfg.N k ^ (η - 2 * cfg.κ * s₀ + cfg.κ * s) := by
        rw [show (cfg.N k ^ η * cfg.N k ^ (-(2 * cfg.κ * s₀))) *
            (cfg.K k * cfg.N k ^ (cfg.κ * s)) =
            cfg.K k * ((cfg.N k ^ η * cfg.N k ^ (-(2 * cfg.κ * s₀))) * cfg.N k ^ (cfg.κ * s)) by ring,
          ← Real.rpow_add hN, ← Real.rpow_add hN]
        congr 1
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hN1 k) hfirstexp) hK0
  have hsecond : cfg.N k ^ (-(s₀ * m / 4)) ≤ cfg.K k * cfg.N k ^ (-(s - s₀) - g) := by
    exact (Real.rpow_le_rpow_of_exponent_le (hN1 k) hsecondexp).trans
      (le_mul_of_one_le_left (by positivity) hK)
  calc
    _ ≤ cfg.K k * cfg.N k ^ (-(s - s₀) - g) + cfg.K k * cfg.N k ^ (-(s - s₀) - g) :=
      add_le_add hfirst hsecond
    _ = 2 * cfg.K k * cfg.N k ^ (-(s - s₀) - g) := by ring
    _ ≤ _ := by simpa only [pow_one] using hk.le

theorem Prepared.eventually_velocity_scalar_error (h : cfg.Prepared) {s₀ s M : ℝ}
    (hs₀ : 0 < s₀)
    (hnear : s - s₀ ≤ s₀ * min cfg.κ (1 - 2 * cfg.κ) / 16)
    (hM : 100 * s₀ < M) :
    ∀ᶠ k in atTop, 72 * cfg.K k ^ 4 * cfg.N k ^ (-M) / cfg.N k ^ (-s₀) ≤
      cfg.N k ^ (-(s - s₀)) := by
  have hm1 : min cfg.κ (1 - 2 * cfg.κ) ≤ 1 := (min_le_left _ _).trans h.rate_le_one
  have hh := mul_le_mul_of_nonneg_left hm1 hs₀.le
  have hgap : -M + s₀ < -(s - s₀) := by linarith
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  filter_upwards [eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    4 hgap (show (0 : ℝ) ≤ 72 by norm_num)] with k hk
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hAi : (cfg.N k ^ (-s₀))⁻¹ = cfg.N k ^ s₀ := by
    rw [Real.rpow_neg hN.le, inv_inv]
  have heq : 72 * cfg.K k ^ 4 * cfg.N k ^ (-M) / cfg.N k ^ (-s₀) =
      72 * cfg.K k ^ 4 * cfg.N k ^ (-M + s₀) := by
    rw [div_eq_mul_inv, hAi, mul_assoc, ← Real.rpow_add hN]
  exact heq.le.trans hk.le

/-- All fitted native scalar errors, including the original reconstruction
and corrected contact direction, fit in the terminal width with any power loss. -/
theorem Prepared.eventually_corrected_scalar_error_bound (h : cfg.Prepared) {s₀ s M η ε : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s)
    (hnear : s - s₀ ≤ s₀ * min cfg.κ (1 - 2 * cfg.κ) / 16)
    (hM : 100 * s₀ < M) (hη : η ≤ s₀ * min cfg.κ (1 - 2 * cfg.κ) / 16) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ a : cfg.AssignmentLevel k s,
      (cfg.K k * cfg.N k ^ (-s) + 72 * cfg.K k ^ 4 * cfg.N k ^ (-M)) / cfg.N k ^ (-s₀) +
        (cfg.N k ^ η * cfg.N k ^ (-(2 * cfg.κ * s₀)) / cfg.timeLength k s +
          cfg.N k ^ (-(s₀ * min cfg.κ (1 - 2 * cfg.κ) / 4))) ≤
            cfg.N k ^ ε * cfg.N k ^ (-(s - s₀)) := by
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hslack := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    1 (show (0 : ℝ) < ε from hε) (show (0 : ℝ) ≤ 3 by norm_num)
  filter_upwards [h.eventually_terminal_collapse_error hs₀ hs hnear hη,
    h.eventually_velocity_scalar_error hs₀ hnear hM, hslack] with k hc hv hslack
  intro a
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hw : cfg.N k ^ (-s) / cfg.N k ^ (-s₀) = cfg.N k ^ (-(s - s₀)) := by
    rw [← Real.rpow_sub hN]
    congr 1
    ring
  have hcoef : cfg.K k + 2 ≤ cfg.N k ^ ε := by
    have hh : 3 * cfg.K k ≤ cfg.N k ^ ε := by simpa only [pow_one, Real.rpow_zero, mul_one] using hslack.le
    linarith only [hK, hh]
  rw [add_div, mul_div_assoc, hw]
  calc
    _ ≤ cfg.K k * cfg.N k ^ (-(s - s₀)) + cfg.N k ^ (-(s - s₀)) +
        cfg.N k ^ (-(s - s₀)) := add_le_add (add_le_add le_rfl hv) (hc a)
    _ = (cfg.K k + 2) * cfg.N k ^ (-(s - s₀)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
