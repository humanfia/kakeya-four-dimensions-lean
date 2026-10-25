/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/PairedDirectionalRow.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeDirectionalAsymptotic
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeScalarFit
import Submission.Obl.k4_subcritical_corrected_scalar_charts.DirectionalMargins

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- A paired fine endpoint row fits the coarse native time signal with a
fixed positive-power accuracy. Both true entries and their ancestry are original. -/
theorem Prepared.eventually_paired_directional_row (h : cfg.Prepared) {s₀ ε : ℝ}
    (hs₀ : 0 < s₀) (hε : 0 < ε)
    (hsmall : ε ≤ s₀ * min cfg.κ (1 - 2 * cfg.κ) / 16) :
    ∀ᶠ k in atTop,
      ∀ (parent : cfg.NativeLevel k s₀) (child : cfg.NativeLevel k (3 * s₀ / 2))
        (ip : Fin (cfg.n k s₀)) (ic : Fin (cfg.n k (3 * s₀ / 2))),
      cfg.A k (3 * s₀ / 2) ic ⊆ cfg.A k s₀ ip →
      I (cfg.T k (3 * s₀ / 2)) (cfg.j k (3 * s₀ / 2) ic) ⊆ I (cfg.T k s₀) (cfg.j k s₀ ip) →
      ∀ (H0 Hb : Fin 6 → ℝ) (v p₀ q₀ t : ℝ),
      t ∈ Icc (0 : ℝ) 1 →
      t ∈ I (cfg.T k (3 * s₀ / 2)) (cfg.j k (3 * s₀ / 2) ic) →
      (∀ p ∈ Icc p₀ (p₀ + cfg.N k ^ (-(2 * cfg.κ * (3 * s₀ / 2)))),
        ∀ q ∈ Icc q₀ (q₀ + cfg.N k ^ (-(2 * cfg.κ * (3 * s₀ / 2)))),
        |cfg.nativeParameter k (3 * s₀ / 2) ic v t p q - predictor Hb t p q| ≤
          cfg.N k ^ ε * cfg.N k ^ (-(3 * s₀ / 2))) →
      |nativeFiberSignal H0 (parent.L ip) (cfg.N k ^ (-(2 * cfg.κ * s₀)))
          (cfg.N k ^ (-s₀)) t -
        (cfg.N k ^ (-(2 * cfg.κ * s₀)) / cfg.N k ^ (-s₀)) *
          fiberDerivative (Hb - H0) t| ≤
        cfg.N k ^ (-(s₀ * min cfg.κ (1 - 2 * cfg.κ) / 4)) := by
  filter_upwards [h.eventually_child_parent_direction hs₀ (show s₀ ≤ 3 * s₀ / 2 by linarith) hε,
    h.eventually_fine_row_error hs₀ hsmall] with k hdir hnum
  intro parent child ip ic hA hI H0 Hb v p₀ q₀ t ht htI hfull
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hD : 0 < cfg.N k ^ (-(2 * cfg.κ * (3 * s₀ / 2))) := Real.rpow_pos_of_pos hN _
  have hr : 0 ≤ cfg.N k ^ (-(2 * cfg.κ * s₀)) / cfg.N k ^ (-s₀) := by positivity
  have htrue := hdir parent child ip ic hA hI t htI
  have htrue' : |(parent.L ip 2 + t * parent.L ip 3) -
      (child.L ic 2 + t * child.L ic 3)| ≤
        cfg.N k ^ ε * cfg.N k ^ (-s₀) / cfg.timeLength k (3 * s₀ / 2) := by
    simpa only [abs_sub_comm] using htrue
  have hfull' := child.directional_comparison ic hD ht hfull
  have hh := directional_signal_comparison (H0 := H0) (v := v) hr htrue' hfull'
  exact hh.trans (by simpa only [mul_assoc] using hnum child.assignments)

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
