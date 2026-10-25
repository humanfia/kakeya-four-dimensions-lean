import Submission.Obl.k4_scalar_guarded_entropic_path.LayerBounds
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.GeometryCharts
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ViewCharts

/-! Calibrate the SAME immutable original geometry used by the point
readouts, directly from its original full TRUE chart and finite guard. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.OriginalView

open MeasureTheory Set PathMeasures
open Submission.Obl.k4_scalar_linear_critical_extremizers

noncomputable section

variable {root final : Code} {D S₀ η : ℝ}

theorem original_geometry_block_bounds (a : OriginalView root final D S₀ η)
    (inner : ℕ) (j : Fin a.count) {G : ℕ} {ε κ gain β loss B : ℝ}
    (Q : a.ChartAt ε inner j) (hQ : ChartGeometry.ofChart Q = a.geometry inner j)
    (hG : a.complexity ≤ G) (hε : ε ≤ loss)
    (hguard : ∀ h : ℝ, h ≤ κ * a.depth j - gain →
      ¬Split.Chart a.parent G (a.depth j) (Split.L a.parent) h loss false
        (a.suffixChain.sample inner))
    (htime : a.time j + ε ≤ κ * a.depth j + β)
    (hβ : Split.N a.parent (a.suffixChain.sample inner) ^ β ≤ B)
    (hgain : Split.N a.parent (a.suffixChain.sample inner) ^ gain ≤ B) :
    Split.N a.parent (a.suffixChain.sample inner) ^ (κ * a.depth j) / B ≤
        (2 : ℝ) ^ (a.geometry inner j).generation ∧
      (2 : ℝ) ^ (a.geometry inner j).generation ≤
        B * Split.N a.parent (a.suffixChain.sample inner) ^ (κ * a.depth j) := by
  have hN : 1 ≤ Code.N a.parent (a.suffixChain.sample inner) := exact_N_ge_one a.parent_exact _
  have h := layer_block_bounds (F := Layer.ofChart Q) hN Q.hcd hG hε hguard htime hβ hgain
  have hT : Q.T = (a.geometry inner j).generation := congrArg ChartGeometry.Geometry.generation hQ
  simpa only [Layer.T, Layer.ofChart, hT, Code.N, Split.N] using h

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.OriginalView
