import Submission.Obl.k4_critical_conditional_row_preparation.HistoryAtomicCaps
import Submission.Obl.k4_critical_conditional_row_preparation.Numerics

namespace Submission.Obl.k4_critical_conditional_row_preparation
noncomputable section
open MeasureTheory Set Filter
namespace Data
variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- Original nesting and original whole-block fits supply a measurable finite
history with bounded affine entries, before any current measure is selected. -/
theorem Valid.eventually_history_data (h : cfg.Valid) (s : ℝ) (hs : 0 < s)
    (hU : 3 * s ≤ cfg.U) : ∀ᶠ k in atTop, Nonempty (cfg.HistoryData k s) := by
  let R := 2 + s⁻¹
  have hR : 1 < R := by dsimp [R]; linarith [inv_pos.mpr hs]
  have hRs : R⁻¹ ≤ s := by
    apply (inv_le_comm₀ (by linarith : 0 < R) hs).mpr
    dsimp [R]
    linarith
  filter_upwards [h.eventually_assignment_level (show 0 < 3 * s by positivity) hU,
    h.nested R hR] with k deep hnest
  classical
  have hn := hnest s (3 * s) hRs (by linarith) hU
  choose parent hA hI using hn
  have he := fun i => deep.exists_bounded_entry h (show 0 ≤ 3 * s by positivity) i
  choose entry hbound hfit using he
  exact ⟨⟨parent, hA, hI, entry, hbound, hfit⟩⟩

end Data
end
end Submission.Obl.k4_critical_conditional_row_preparation
