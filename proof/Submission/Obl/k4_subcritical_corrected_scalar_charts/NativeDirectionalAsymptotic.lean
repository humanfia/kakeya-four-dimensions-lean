/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeDirectionalAsymptotic.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeAsymptotic
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeDirection

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter
open Submission.Obl.k4_critical_intercept_concentration.Data
open Submission.Obl.k4_profile_density_bounds

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The actual native ancestral entries differ in the contact direction by
at most the coarse hidden width divided by the child horizontal scale. -/
theorem Prepared.eventually_child_parent_direction (h : cfg.Prepared) {s₀ s ε : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      ∀ (parent : cfg.NativeLevel k s₀) (child : cfg.NativeLevel k s)
        (ip : Fin (cfg.n k s₀)) (ic : Fin (cfg.n k s)),
      cfg.A k s ic ⊆ cfg.A k s₀ ip →
      I (cfg.T k s) (cfg.j k s ic) ⊆ I (cfg.T k s₀) (cfg.j k s₀ ip) →
      ∀ t ∈ I (cfg.T k s) (cfg.j k s ic),
        |(child.L ic 2 + t * child.L ic 3) - (parent.L ip 2 + t * parent.L ip 3)| ≤
          cfg.N k ^ ε * cfg.N k ^ (-s₀) / cfg.timeLength k s := by
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hslack := eventually_subpower_mul_rpow_lt hN1 h.scale_limit h.subpower.1 h.subpower.2
    1 (show (0 : ℝ) < ε / 2 by positivity) (show (0 : ℝ) ≤ 6 by norm_num)
  filter_upwards [h.eventually_child_parent_norm hs₀ hs (show 0 < ε / 2 by positivity),
    hslack] with k hnorm hslack
  intro parent child ip ic hA hI t ht
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hK0 : 0 ≤ cfg.K k := zero_le_one.trans hK
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hq : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  have ht' : (((cfg.j k s ic : ℕ) : ℝ) * cfg.timeLength k s ≤ t) ∧
      t ≤ (((cfg.j k s ic : ℕ) : ℝ) + 1) * cfg.timeLength k s := by
    simpa only [I, timeLength, mem_Icc, div_eq_mul_inv] using ht
  have htime : |t - cfg.nativeMidpoint k s ic| ≤ cfg.timeLength k s := by
    rw [abs_le]
    dsimp [nativeMidpoint]
    constructor <;> linarith
  have htilt : |cfg.c k s ic 4 - cfg.nativeMidpoint k s ic| ≤
      cfg.K k * cfg.timeLength k s := by
    have hc := child.assignments.plane_center ic
    dsimp [nativeMidpoint]
    linarith [abs_nonneg (cfg.c k s ic 3 + cfg.c k s ic 0 +
      (((cfg.j k s ic : ℕ) : ℝ) + 1 / 2) * cfg.timeLength k s * cfg.c k s ic 1)]
  have hh := horizontal_slope_of_atlas_norm (child.L ic - parent.L ip)
    (cfg.c k s ic) hq hK0 htime htilt (hnorm parent child ip ic hA hI)
  have hslack' : 2 * (cfg.K k + 2) ≤ cfg.N k ^ (ε / 2) := by
    have hh : 2 * (cfg.K k + 2) ≤ 6 * cfg.K k := by linarith
    exact hh.trans (by simpa only [pow_one, Real.rpow_zero, mul_one] using hslack.le)
  have heq : (child.L ic - parent.L ip) 2 + t * (child.L ic - parent.L ip) 3 =
      (child.L ic 2 + t * child.L ic 3) - (parent.L ip 2 + t * parent.L ip 3) := by
    simp only [Pi.sub_apply]
    ring
  rw [heq] at hh
  refine hh.trans ?_
  calc
    _ ≤ (cfg.N k ^ (ε / 2) * (cfg.N k ^ (ε / 2) * cfg.N k ^ (-s₀))) /
        cfg.timeLength k s := by gcongr
    _ = _ := by
      rw [← mul_assoc, ← Real.rpow_add hN, add_halves]

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
