/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeAsymptotic.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeCalibrationLoss
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeResolution
import Submission.Obl.k4_subcritical_corrected_scalar_charts.OriginalCapUse

/-! Whole original ancestor-child comparison with the arbitrary asymptotic
loss exposed. No current paired incidence is used as a witness floor. -/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data
open Submission.Obl.k4_profile_density_bounds

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Original nesting and the original joint caps bound the affine difference
on the entire normalized child unit box, with any prescribed power loss. -/
theorem Prepared.eventually_child_parent_norm (h : cfg.Prepared) {s₀ s ε : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      ∀ (parent : cfg.NativeLevel k s₀) (child : cfg.NativeLevel k s)
        (ip : Fin (cfg.n k s₀)) (ic : Fin (cfg.n k s)),
      cfg.A k s ic ⊆ cfg.A k s₀ ip →
      I (cfg.T k s) (cfg.j k s ic) ⊆ I (cfg.T k s₀) (cfg.j k s₀ ip) →
      ∀ z : Fin 3 → ℝ,
        (∀ e, |atlasFrame (cfg.timeLength k s) (cfg.nativeMidpoint k s ic)
          (cfg.c k s ic) z e| ≤ 1) →
        |affineField (child.L ic - parent.L ip) z| ≤
          cfg.N k ^ ε * cfg.N k ^ (-s₀) := by
  obtain ⟨C, L, hC, hL, hcal⟩ := exists_original_child_calibration
  let A := (128 * (8847360 : ℝ) ^ 3) * C
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hspos : 0 < s := hs₀.trans_le hs
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hsmall := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    33 (show -(10 * s) < 0 by linarith) (show 0 ≤ 2 * L * A by positivity)
  have hbound := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    34 (show (0 : ℝ) < ε from hε) (show 0 ≤ 16 * A by positivity)
  filter_upwards [h.eventually_native_mesh hspos,
    h.eventually_original_hidden_caps (show 0 < 40 * s by positivity) hspos.le,
    hsmall, hbound] with k hmesh hcap hsmall hbound
  intro parent child ip ic hassign htime z hz
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hK0 : 0 ≤ cfg.K k := zero_le_one.trans hK
  have hq : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  have ha : 0 < cfg.N k ^ (-s) := Real.rpow_pos_of_pos hN _
  have hA₀ : 0 < cfg.N k ^ (-s₀) := Real.rpow_pos_of_pos hN _
  have hδ : 0 < cfg.N k ^ (-(40 * s)) := Real.rpow_pos_of_pos hN _
  have hσ : 0 < cfg.N k ^ (-(10 * s)) := Real.rpow_pos_of_pos hN _
  have hloss : nativeOriginalLoss C (cfg.K k) ≤ A * cfg.K k ^ 33 :=
    nativeOriginalLoss_bound hC.le hK
  have hloss0 : 0 ≤ nativeOriginalLoss C (cfg.K k) := by
    rw [nativeOriginalLoss_formula hK]
    positivity
  have hsmall' : L * nativeOriginalLoss C (cfg.K k) * cfg.N k ^ (-(10 * s)) ≤ 1 / 2 := by
    have hb : L * nativeOriginalLoss C (cfg.K k) * cfg.N k ^ (-(10 * s)) ≤
        L * (A * cfg.K k ^ 33) * cfg.N k ^ (-(10 * s)) := by gcongr
    simp only [Real.rpow_zero] at hsmall
    nlinarith
  have hnorm := hcal α cfg h k s₀ s parent child ip ic hassign htime
    (cfg.N k ^ (-(40 * s))) (cfg.N k ^ (-(10 * s))) 1 hδ hσ
    (hmesh child.assignments).2.1 le_rfl (hmesh child.assignments).1 hcap
    ((hmesh child.assignments).2.2 ic) (by
      rw [original_native_loss_cancellation C (cfg.K k) (cfg.timeLength k s)
        (cfg.N k ^ (-s)) cfg.d hq ha]
      exact hsmall') z hz
  rw [original_native_loss_cancellation C (cfg.K k) (cfg.timeLength k s)
    (cfg.N k ^ (-s)) cfg.d hq ha] at hnorm
  have haa : cfg.N k ^ (-s) ≤ cfg.N k ^ (-s₀) :=
    Real.rpow_le_rpow_of_exponent_le (hN1 k) (neg_le_neg hs)
  have hcoef : 16 * nativeOriginalLoss C (cfg.K k) * cfg.K k ≤ cfg.N k ^ ε := by
    calc
      _ ≤ 16 * (A * cfg.K k ^ 33) * cfg.K k := by gcongr
      _ = 16 * A * cfg.K k ^ 34 := by ring
      _ ≤ cfg.N k ^ ε := by simpa only [Real.rpow_zero, mul_one] using hbound.le
  calc
    _ ≤ 8 * 1 * nativeOriginalLoss C (cfg.K k) *
        (cfg.K k * (cfg.N k ^ (-s) + cfg.N k ^ (-s₀))) := hnorm
    _ ≤ (16 * nativeOriginalLoss C (cfg.K k) * cfg.K k) * cfg.N k ^ (-s₀) := by
      have hh := mul_le_mul_of_nonneg_left (add_le_add_right haa (cfg.N k ^ (-s₀)))
        (show 0 ≤ 8 * nativeOriginalLoss C (cfg.K k) * cfg.K k by positivity)
      convert hh using 1 <;> ring
    _ ≤ cfg.N k ^ ε * cfg.N k ^ (-s₀) := mul_le_mul_of_nonneg_right hcoef hA₀.le

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
