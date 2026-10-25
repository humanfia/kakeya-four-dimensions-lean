import Submission.Obl.k4_finite_width_path_realization.SplitInterfaces
import Submission.Obl.k4_true_forest_own_depth_preparation
import Submission.Obl.k4_raw_critical_segment_forests
import Submission.Obl.k4_finite_forest_width_selection

namespace Submission.Obl.k4_finite_width_path_realization

theorem preparation_child : ForestPreparationExpanded := by
  exact Submission.k4_true_forest_own_depth_preparation

theorem raw_forests_child : RawCriticalForestsExpanded := by
  exact Submission.k4_raw_critical_segment_forests

theorem width_selection_child : ForestWidthSelectionExpanded := by
  exact Submission.k4_finite_forest_width_selection

end Submission.Obl.k4_finite_width_path_realization
