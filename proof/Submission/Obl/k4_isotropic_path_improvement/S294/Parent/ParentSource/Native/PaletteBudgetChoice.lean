-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PaletteBudgetChoice, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PaletteBudgetChoice.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PaletteBudgetChoice.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204/x0749, commit 6f2478eeecc213e54a9862f7bddfc3321aef9b01;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PaletteBudgetChoice.lean. General numerical proofs are imported from accepted lib.

import Mathlib.Basic.ENNReal.Inv
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Submission.Lib.K4NativePreparationNumerics.PaletteBudgetChoice

/-! General native preparation helpers imported from gate-accepted library g00875. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

export Submission.Lib.K4NativePreparationNumerics (
  lightParentThreshold
  palettePruningThreshold
  lightParentThreshold_ne_zero
  lightParentThreshold_ne_top
  palettePruningThreshold_pos
  lightParentThreshold_cost
  palettePruningThreshold_cost
  native_palette_budget_choices
  lightParentThreshold_inv
  angular_threshold_inv
  native_angular_cap_coefficient)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
