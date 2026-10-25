import Submission.Obl.k4_horizontal_coefficient_count.DepthContact
import Submission.Obl.k4_horizontal_coefficient_count.SupportAssembly
import Submission.Obl.k4_critical_switching_state_preparation.NativeCellCaps

namespace Submission.Obl.k4_horizontal_coefficient_count

/-- Whole true witnesses and original scalar bins give the support count
needed by the accepted scalar coefficient clustering estimate. -/
theorem supportCount_of_hyp {α : Type} [MeasurableSpace α]
    (D : DepthData α) (h : D.Hyp) : D.SupportCount (6442450944 * D.K ^ 17) := by
  have hK : 0 ≤ D.K := by linarith [h.hK]
  have hh := DepthData.supportCount_of_block_counts h
    (C := 33554432 * D.K ^ 15) (by positivity)
    (fun g j S hS => h.block_label_count g j S hS)
    Submission.Obl.k4_critical_switching_state_preparation.scalar_interval_bin_cover
  have heq : 3 * 64 * (33554432 * D.K ^ 15) * D.K ^ 2 =
      6442450944 * D.K ^ 17 := by ring
  simpa only [heq] using hh

end Submission.Obl.k4_horizontal_coefficient_count
