/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at a5c0b1bcb6dacb66c2e29bec68dd8eae37c23e9d, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeComparisonData.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeComparisonContext
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeMarkedComparison

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_derivative_evaluation_lists
open Submission.Obl.k4_row_cell_regularization

noncomputable section

attribute [local instance] sum_measurableSingletonClass

namespace NativeComparisonData

variable {α : Type} [MeasurableSpace α] {cfg : NativeModel α}
  {k : ℕ} {s : ℝ} {σ : Measure (α × ℝ)} (c : NativeComparisonData cfg k s σ)

/-- The concrete marked input with all original-law certificates supplied. -/
def comparison : MarkedComparison (α × ℝ) (Fin c.support.table.count) c.Index c.Colour := by
  letI := c.finite_original
  letI := c.finite_palette
  exact cfg.nativeMarkedComparison c.support c.layer c.measurable_b c.dominated c.caps
    c.re_lower c.re_upper c.velocity_lower c.velocity_upper c.width_lower c.width_upper
    c.L c.slopes c.true_fit c.N_pos c.K_one c.M_nonneg c.D_pos c.D_one
    (Real.rpow_pos_of_pos c.N_pos _) (c.velocity_width.trans c.D_one) rfl
    c.mesh_one c.mesh_time c.mesh_room c.source_fit c.witness_fit c.round_cell c.round_jitter

theorem comparison_density (l : c.Colour) :
    c.comparison.density l = 28672 * cfg.K k * c.A ^ cfg.d *
      cfg.timeLength k s * c.D ^ 2 * binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀)) (l.1 0) := by
  change (7 * (cfg.K k * c.A ^ cfg.d * binWeight (cfg.π k) (cfg.N k ^ (-cfg.e₀)) (l.1 0))) *
    (16 * cfg.timeLength k s * (16 * c.D) ^ 2) = _
  ring

end NativeComparisonData

end

end Submission.Obl.k4_horizontal_strict_parameter_step
