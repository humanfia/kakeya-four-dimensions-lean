/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/CorrectionLosses.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeResolution

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Filter
open Submission.Obl.k4_profile_density_bounds

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Explicit losses for the original-prior correction selection. A paired
sample at loss `ε` suffices for correction coefficients and retained mass at
loss `10 ε`. -/
theorem Prepared.eventually_correction_losses (h : cfg.Prepared) {s₀ ε : ℝ}
    (hs₀ : 0 < s₀) (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      2 * cfg.N k ^ (-(3 * ε)) ≤ cfg.N k ^ (-(2 * ε)) ∧
      17 * (96 * cfg.K k / cfg.N k ^ (-(3 * ε))) ^ 2 *
        (6 * cfg.N k ^ ε + cfg.N k ^ (-(s₀ * min cfg.κ (1 - 2 * cfg.κ) / 4))) ≤
          cfg.N k ^ (10 * ε) ∧
      cfg.N k ^ (-(10 * ε)) ≤ (cfg.N k ^ (-(3 * ε))) ^ 3 / (8 * cfg.K k ^ 2) := by
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hfirst := eventually_const_mul_rpow_lt h.scale_limit
    (show -(3 * ε) < -(2 * ε) by linarith) 2
  have hcoef := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    2 (show 7 * ε < 10 * ε by linarith) (show (0 : ℝ) ≤ 1096704 by norm_num)
  have hmass := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    2 (show -(10 * ε) < -(9 * ε) by linarith) (show (0 : ℝ) ≤ 8 by norm_num)
  filter_upwards [hfirst, hcoef, hmass] with k hfirst hcoef hmass
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have hm : 0 < min cfg.κ (1 - 2 * cfg.κ) := lt_min h.rate_pos (by linarith [h.subcritical_rate])
  have hδ : cfg.N k ^ (-(s₀ * min cfg.κ (1 - 2 * cfg.κ) / 4)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (neg_nonpos.mpr (by positivity))
  have hB : 1 ≤ cfg.N k ^ ε := Real.one_le_rpow (hN1 k) hε.le
  have hInv : (cfg.N k ^ (-(3 * ε)))⁻¹ = cfg.N k ^ (3 * ε) := by
    rw [Real.rpow_neg hN.le, inv_inv]
  have hpow : (cfg.N k ^ (3 * ε)) ^ 2 * cfg.N k ^ ε = cfg.N k ^ (7 * ε) := by
    rw [pow_two, mul_assoc, ← Real.rpow_add hN, ← Real.rpow_add hN]
    congr 1
    ring
  have hcube : (cfg.N k ^ (-(3 * ε))) ^ 3 = cfg.N k ^ (-(9 * ε)) := by
    rw [pow_succ, pow_two, ← Real.rpow_add hN, ← Real.rpow_add hN]
    congr 1
    ring
  refine ⟨hfirst.le, ?_, ?_⟩
  · calc
      _ ≤ 17 * (96 * cfg.K k / cfg.N k ^ (-(3 * ε))) ^ 2 * (7 * cfg.N k ^ ε) := by
        gcongr
        linarith
      _ = 1096704 * cfg.K k ^ 2 * cfg.N k ^ (7 * ε) := by
        rw [div_eq_mul_inv, hInv, ← hpow]
        ring
      _ ≤ _ := hcoef.le
  · rw [hcube]
    apply (le_div_iff₀ (show (0 : ℝ) < 8 * cfg.K k ^ 2 by positivity)).mpr
    convert hmass.le using 1 <;> ring

theorem Prepared.eventually_corrected_chart_budget (h : cfg.Prepared) {ε ξ : ℝ}
    (hε : 0 < ε) (hgap : 10 * ε < ξ) :
    ∀ᶠ k in atTop, cfg.N k ^ ε + 3 * cfg.N k ^ (10 * ε) ≤ cfg.N k ^ ξ ∧
      2 * cfg.K k ≤ cfg.N k ^ ξ := by
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hsum := eventually_const_mul_rpow_lt h.scale_limit hgap 4
  have hcoef := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    1 (show 0 < ξ by linarith) (show (0 : ℝ) ≤ 2 by norm_num)
  filter_upwards [hsum, hcoef] with k hsum hcoef
  have he : cfg.N k ^ ε ≤ cfg.N k ^ (10 * ε) :=
    Real.rpow_le_rpow_of_exponent_le (hN1 k) (by linarith)
  exact ⟨(by linarith), by simpa only [pow_one, Real.rpow_zero, mul_one] using hcoef.le⟩

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
