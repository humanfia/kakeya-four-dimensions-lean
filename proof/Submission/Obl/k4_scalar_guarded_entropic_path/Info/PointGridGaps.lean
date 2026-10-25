import Submission.Obl.k4_scalar_guarded_entropic_path.Info.PointWindowIndices
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ViewGrid

/-! The actual common parent grid supplies the coarse fit and fine
separation margins, while its small node spacing remains unchanged. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open PathGeometry PathGeometry.PathMeasures
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

variable {root final : Code} {D S₀ η₀ : ℝ}

/-- The fixed half-window choice works in EVERY actual parent whose
original grid has the stated approximation error. -/
theorem point_grid_depth_gaps (a : OriginalView root final D S₀ η₀)
    {κ η scale Δ baseLength error v : ℝ} {m : ℕ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hη : 0 < η) (hscale : 0 ≤ scale)
    (herror : 0 ≤ error) (herrorScale : error ≤ scale) (hv : v ≤ scale)
    (hstep : Δ * baseLength = scale * η)
    (hcount : 2 * pointHalfWindow κ η m ≤ a.count)
    (hgrid : PathNodes.TrueGridPath.GridControl a κ Δ baseLength error) :
    scale * ((m : ℝ) + 1) ≤ a.depth
        (pointCoarseIndex (pointHalfWindow κ η m) (pointHalfWindow_pos κ η m) hcount) ∧
      scale * ((m : ℝ) + 1) ≤ κ *
        (a.depth (pointFineIndex (pointHalfWindow κ η m) (pointHalfWindow_pos κ η m) hcount) -
          a.depth (pointCoarseIndex (pointHalfWindow κ η m) (pointHalfWindow_pos κ η m) hcount)) - 2 * v := by
  let q := pointHalfWindow κ η m
  have hq : 0 < q := pointHalfWindow_pos κ η m
  let c := pointCoarseIndex q hq hcount
  let f := pointFineIndex q hq hcount
  have hcn : (c.val : ℝ) + 1 = (q : ℝ) := by
    exact_mod_cast point_coarse_step hq hcount
  have hfn : (f.val : ℝ) + 1 = 2 * (q : ℝ) := by
    exact_mod_cast point_fine_future hq hcount
  have hc := (hgrid c).1
  have hf := (hgrid f).1
  have hceq : ((c.val : ℝ) + 1) * Δ * baseLength = scale * ((q : ℝ) * η) := by
    rw [hcn, mul_assoc, hstep]
    ring
  have hfeq : ((f.val : ℝ) + 1) * Δ * baseLength = 2 * scale * ((q : ℝ) * η) := by
    rw [hfn, mul_assoc, hstep]
    ring
  rw [hceq] at hc
  rw [hfeq] at hf
  exact point_window_depth_gaps hκ hκ1 (mul_nonneg (Nat.cast_nonneg q) hη.le)
    hscale herror herrorScale hv (pointHalfWindow_gap hκ hη m) hc hf

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
