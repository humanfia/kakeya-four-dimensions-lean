/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/TrueSaturation.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RefinementSubfamilies
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathBudgets

/-! True selected-incidence floors imply full-prior saturation. Later
incidence restrictions preserve this prior bound through RetainedRefinement. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

theorem RefinementWitness.saturated_of_true_charts {p q : Code} {r b h : ℝ}
    (w : RefinementWitness p q r b h) (hp : Exact p)
    (htrue : ∀ k, ChartData p w.exponent r b (h + w.loss k) (w.loss k) true
      (w.sample k) (w.T k) (W q k) (w.world k) (w.block k) (w.assignment k)
        (w.selected k) (w.center k) (w.speed k) (w.width k) (w.polynomial k) (w.lists k)) :
    w.toRefinementData.Saturated r w.loss := by
  intro k i
  have hN : 0 < N p (w.sample k) := by linarith [hp.1.1 (w.sample k)]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hfloor⟩ := (htrue k).2.2.2.2.2.1 i
  have hq := w.duration_pos k
  have hscale : w.toRefinementData.duration k *
      (N p (w.sample k) ^ (-f p r - w.loss k) * w.width k i) =
      N p (w.sample k) ^ (-f p r) * w.width k i /
        (N p (w.sample k) ^ w.loss k * (2 : ℝ) ^ w.T k) := by
    rw [Real.rpow_sub hN]
    unfold RefinementData.duration
    ring
  have hmass : ENNReal.ofReal (w.toRefinementData.duration k) *
      ENNReal.ofReal (N p (w.sample k) ^ (-f p r - w.loss k) * w.width k i) ≤
      ENNReal.ofReal (w.toRefinementData.duration k) *
        ν p (w.sample k) (w.world k i) (w.assignment k i) := by
    rw [← ENNReal.ofReal_mul hq.le, hscale]
    exact (hfloor rfl).trans (PathMeasures.selected_le_prior_budget w k i)
  have h := mul_le_mul'
    (show (ENNReal.ofReal (w.toRefinementData.duration k))⁻¹ ≤
      (ENNReal.ofReal (w.toRefinementData.duration k))⁻¹ from le_rfl) hmass
  simpa only [← mul_assoc,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top,
    one_mul] using h

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
