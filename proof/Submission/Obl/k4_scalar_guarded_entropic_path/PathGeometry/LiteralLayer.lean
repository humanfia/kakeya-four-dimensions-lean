/-
Adapted from this LOT tree, obligation o093, session x0535, commit 21cac614,
Submission/Obl/k4_scalar_critical_path_terminal/LiteralLayer.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.LiteralCoarsening

/-! A layer's relative profile proves exactness of the literal same-law
outer problem. No identification of an existential outer code is required. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.LayerAt

open Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

theorem literal_outer_exact {p outer q : Code} {r h δ : ℝ}
    (layer : LayerAt p outer q r h δ) (hp : Exact p) :
    Exact (literalCoarsen p r δ) := by
  have hr : 0 < r := by
    rw [← layer.outer_length]
    exact exact_length_pos layer.outer_exact
  have hδ0 : 0 ≤ δ := by
    rw [← layer.outer_cap]
    exact (exact_dimension_bounds layer.outer_exact).1
  have hδ1 : δ < 1 := by
    rw [← layer.outer_cap]
    exact (exact_dimension_bounds layer.outer_exact).2
  apply Submission.Obl.k4_scalar_chart_normalization.exact_coarsen hp hr layer.depth_lt hδ0 hδ1
  intro s hs hsr
  have hcap := exact_terminal_cap layer.outer_exact s hs (by rw [layer.outer_length]; exact hsr)
  have hprof0 := layer.outer_profile r ⟨hr.le, le_rfl⟩
  have hprofs := layer.outer_profile s ⟨hs, hsr⟩
  rw [layer.outer_length, layer.outer_cap] at hcap
  change f p r - f p s ≤ δ * (r - s)
  linarith

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.LayerAt
