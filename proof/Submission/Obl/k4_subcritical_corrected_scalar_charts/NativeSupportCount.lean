/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeSupportCount.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeBandCount
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeResolution

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data
open Submission.Obl.k4_profile_density_bounds

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The original descendants contained in one native box have the scalar
support count (A0/ai)^d, up to any prescribed power loss. All witnesses and
floors precede the chart restriction that produced this finite list. -/
theorem Prepared.eventually_descendant_count (h : cfg.Prepared) {s₀ s ε : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hε : 0 < ε) (p : ℕ) :
    ∀ᶠ k in atTop,
      ∀ (parent : cfg.NativeLevel k s₀) (child : cfg.NativeLevel k s)
        (ip : Fin (cfg.n k s₀)) (anchor : Fin (cfg.n k s))
        (S : Finset (Fin (cfg.n k s))),
      (∀ i ∈ S, ∀ y ∈ cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i), ∀ e,
        |atlasFrame (cfg.timeLength k s) (cfg.nativeMidpoint k s anchor)
          (cfg.c k s anchor) (originalBase (cfg.b k y.1) y.2) e| ≤ cfg.K k ^ p) →
      (∀ i ∈ S, cfg.A k s i ⊆ cfg.A k s₀ ip) →
      (∀ i ∈ S, I (cfg.T k s) (cfg.j k s i) ⊆ I (cfg.T k s₀) (cfg.j k s₀ ip)) →
      (S.card : ℝ) ≤ cfg.N k ^ ε *
        ((cfg.N k ^ (-s₀)) / (cfg.N k ^ (-s))) ^ cfg.d := by
  have hspos : 0 < s := hs₀.trans_le hs
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hcoef := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    (5 + 3 * p) (show (0 : ℝ) < ε from hε) (show (0 : ℝ) ≤ 162000 by norm_num)
  filter_upwards [h.eventually_native_mesh hspos,
    h.eventually_original_hidden_caps (show 0 < 40 * s by positivity) hs₀.le,
    hcoef] with k hmesh hcap hcoef
  intro parent child ip anchor S hbox hA hI
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hδ : 0 < cfg.N k ^ (-(40 * s)) := Real.rpow_pos_of_pos hN _
  have hmesh' : 108 * cfg.K k ^ 4 * cfg.N k ^ (-(40 * s)) ≤ cfg.N k ^ (-s₀) :=
    (hmesh child.assignments).1.trans
      (Real.rpow_le_rpow_of_exponent_le (hN1 k) (neg_le_neg hs))
  have hresolve : ∀ e, (∑ j, |nativeFrameMatrix (cfg.timeLength k s)
      (cfg.c k s anchor 1) (-cfg.c k s anchor 3 - cfg.c k s anchor 4 * cfg.c k s anchor 1)
      (cfg.c k s anchor 4) e j| * cfg.N k ^ (-(40 * s))) ≤ 1 := by
    intro e
    exact ((hmesh child.assignments).2.2 anchor e).trans
      (Real.rpow_le_one_of_one_le_of_nonpos (hN1 k) (by linarith))
  have hc := parent.count_descendants_in_box h child ip S hδ (one_le_pow₀ hK)
    hmesh' hcap (cfg.nativeMidpoint k s anchor) (cfg.c k s anchor 0)
    (cfg.c k s anchor 2 + cfg.c k s anchor 4 * cfg.c k s anchor 0)
    (cfg.c k s anchor 1) (-cfg.c k s anchor 3 - cfg.c k s anchor 4 * cfg.c k s anchor 1)
    (cfg.c k s anchor 4) hresolve hbox hA hI
  have heq : 162000 * cfg.K k ^ 5 * (cfg.K k ^ p) ^ 3 =
      162000 * cfg.K k ^ (5 + 3 * p) := by
    rw [show 5 + 3 * p = 5 + p * 3 by omega, pow_add, pow_mul]
    ring
  rw [heq] at hc
  refine hc.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  simpa only [Real.rpow_zero, mul_one] using hcoef.le

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
