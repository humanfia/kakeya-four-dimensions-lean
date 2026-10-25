/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/ContactMargins.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeResolution
import Submission.Obl.k4_subcritical_corrected_scalar_charts.ChartInterface

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Filter
open Submission.Obl.k4_critical_intercept_concentration
open Submission.Obl.k4_critical_intercept_concentration.Data
open Submission.Obl.k4_profile_density_bounds

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The fixed endpoint depth margins resolve every terminal native contact
box by the scalar mesh and the common velocity bin. -/
theorem Prepared.eventually_scalar_contact_margins (h : cfg.Prepared)
    {s₀ s M : ℝ} (hs₀ : 0 < s₀) (hs : s₀ ≤ s)
    (hnear : s - s₀ ≤ s₀ * min cfg.κ (1 - 2 * cfg.κ) / 16)
    (hM : 100 * s₀ < M) :
    ∀ᶠ k in atTop, ∀ a : cfg.AssignmentLevel k s,
      cfg.N k ^ (-(20 * s₀)) ≤ cfg.timeLength k s ∧
      3 * cfg.N k ^ (-(2 * cfg.κ * s₀)) ≤ cfg.timeLength k s ∧
      cfg.N k ^ (-M) ≤ cfg.N k ^ (-(2 * cfg.κ * s₀)) ∧
      cfg.N k ^ (-M) + cfg.N k ^ (-M) ≤
        cfg.N k ^ (-(2 * cfg.κ * s₀)) * cfg.timeLength k s := by
  have hspos : 0 < s := hs₀.trans_le hs
  have hm1 : min cfg.κ (1 - 2 * cfg.κ) ≤ 1 := (min_le_left _ _).trans h.rate_le_one
  have hnear' : s - s₀ ≤ s₀ / 16 := by
    have hh := mul_le_mul_of_nonneg_left hm1 hs₀.le
    exact hnear.trans (by linarith)
  have hsmax : s < 3 * s₀ / 2 := by linarith
  have hκ : 0 < cfg.κ := h.rate_pos
  have hκs : cfg.κ * s ≤ s := by nlinarith [h.rate_le_one]
  have hκs₀ : cfg.κ * s₀ ≤ s₀ := by nlinarith [h.rate_le_one]
  have hgap₁ : -(20 * s₀) < -cfg.κ * s := by nlinarith
  have hgap₂ : -(2 * cfg.κ * s₀) < -cfg.κ * s := by
    nlinarith [mul_pos hκ (show 0 < 2 * s₀ - s by linarith)]
  have hgap₃ : -M < -(2 * cfg.κ * s₀) - cfg.κ * s := by linarith
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hσ := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    1 hgap₁ (show (0 : ℝ) ≤ 1 by norm_num)
  have hD := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    1 hgap₂ (show (0 : ℝ) ≤ 3 by norm_num)
  have hχ := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    1 hgap₃ (show (0 : ℝ) ≤ 2 by norm_num)
  filter_upwards [hσ, hD, hχ] with k hσ hD hχ
  intro a
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have htime : cfg.N k ^ (-cfg.κ * s) ≤ cfg.K k * cfg.timeLength k s :=
    (time_length_comparison hN hK a.time_lower a.time_upper).2
  simp only [pow_one, one_mul] at hσ hD hχ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mul_le_mul_iff_right₀ hK).mp (by simpa only [mul_comm] using hσ.le.trans htime)
  · apply (mul_le_mul_iff_right₀ hK).mp
    convert hD.le.trans htime using 1 <;> ring
  · apply Real.rpow_le_rpow_of_exponent_le (hN1 k)
    linarith
  · apply (mul_le_mul_iff_right₀ hK).mp
    have hdg : cfg.N k ^ (-(2 * cfg.κ * s₀) - cfg.κ * s) =
        cfg.N k ^ (-(2 * cfg.κ * s₀)) * cfg.N k ^ (-cfg.κ * s) := by
      rw [← Real.rpow_add hN]
      congr 1
      ring
    rw [hdg] at hχ
    have hh := hχ.le.trans (mul_le_mul_of_nonneg_left htime
      (Real.rpow_nonneg hN.le _))
    convert hh using 1 <;> ring

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
