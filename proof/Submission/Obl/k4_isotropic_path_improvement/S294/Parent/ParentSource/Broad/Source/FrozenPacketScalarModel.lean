-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.FrozenPacketScalarModel, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/FrozenPacketScalarModel.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/FrozenPacketScalarModel.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 38d075b9;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenPacketScalarModel.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPacketQuadratics
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPacketLaw
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2.Interface

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPacket

open Set MeasureTheory
open Submission.Lib.K4XInterface

noncomputable section

/-- The actual seven scalar-normal coefficients of one original indexed
line: three native quadratic coefficients and two affine base coordinates. -/
def scalarCoefficients (p : FrozenPacket) (l : Line) : Fin 7 → ℝ :=
  ![p.coefficients l 0, p.coefficients l 1, p.coefficients l 2,
    (p.line l).2 0, (p.line l).2 3, (p.line l).2 1, (p.line l).2 4]

theorem measurable_scalarCoefficients (p : FrozenPacket) : Measurable p.scalarCoefficients := by
  have hq (i : Fin 3) : Measurable (fun l : Line => p.coefficients l i) :=
    (PiLp.continuous_apply 2 _ i).measurable.comp p.measurable_coefficients
  have hc (i : Fin 6) : Measurable (fun l : Line => (p.line l).2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp p.measurable_line)
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · exact hq 0
  · exact hq 1
  · exact hq 2
  · exact hc 0
  · exact hc 3
  · exact hc 1
  · exact hc 4

theorem scalar_x (p : FrozenPacket) (l : Line) (t : ℝ) :
    Jets2.zx (p.scalarCoefficients l) t = p.signalValue l t := by
  rw [p.coefficient_identity]
  dsimp [Jets2.zx, scalarCoefficients]
  ring

theorem scalar_y (p : FrozenPacket) (l : Line) (t : ℝ) :
    Jets2.zy (p.scalarCoefficients l) t = fun i => gy (p.line l) t i := by
  funext i
  fin_cases i <;> simp [Jets2.zy, scalarCoefficients, gy, gx, mul_comm]

theorem scalar_velocity (p : FrozenPacket) (l : Line) :
    Jets2.zv (p.scalarCoefficients l) = fun i => gv (p.line l) i := by
  funext i
  fin_cases i <;> rfl

theorem scalar_x_derivative (p : FrozenPacket) (l : Line) (t : ℝ) :
    p.scalarCoefficients l 1 + 2 * p.scalarCoefficients l 2 * t =
      (p.signal l).derivative.eval t := by
  rw [p.signal_derivative_identity]
  dsimp [scalarCoefficients]
  ring

/-- The actual scalar-normal coefficients are bounded on the FULL old
assignment, independently of the original format exponent. -/
theorem scalar_coefficients_bound (p : FrozenPacket) (l : Line) (hl : l ∈ p.assigned) :
    ∀ i, |p.scalarCoefficients l i| ≤ 17 * p.slack := by
  have hκ : 0 ≤ p.slack :=
    (abs_nonneg (p.signalValue l 0)).trans ((p.native_bounds l hl 0 (by norm_num)).2.1)
  have hc (i : Fin 3) : |p.coefficients l i| ≤ 17 * p.slack :=
    (PiLp.norm_apply_le _ _).trans (p.coefficients_bound l hl)
  have hnative := (p.native_bounds l hl 0 (by norm_num)).1
  have hy : ‖gy (p.line l) 0‖ ≤ 17 * p.slack := by
    linarith [norm_nonneg (gv (p.line l))]
  have hv : ‖gv (p.line l)‖ ≤ 17 * p.slack := by
    linarith [norm_nonneg (gy (p.line l) 0)]
  have hyi (i : Fin 2) : |gy (p.line l) 0 i| ≤ 17 * p.slack :=
    (PiLp.norm_apply_le _ _).trans hy
  have hvi (i : Fin 2) : |gv (p.line l) i| ≤ 17 * p.slack :=
    (PiLp.norm_apply_le _ _).trans hv
  intro i
  fin_cases i
  · exact hc 0
  · exact hc 1
  · exact hc 2
  · simpa [scalarCoefficients, gy, gx] using hyi 0
  · exact hvi 0
  · simpa [scalarCoefficients, gy, gx] using hyi 1
  · exact hvi 1

/-- All later analytical restrictions of the same packet law retain
this actual scalar coefficient geometry and the original trajectory tag. -/
theorem scalar_coefficients_on_original_law (p : FrozenPacket) (ν : Measure Line) :
    ∀ᵐ z ∂p.law ν, ∀ i, |p.scalarCoefficients z.1 i| ≤ 17 * p.slack :=
  (p.law_original_assignment ν).mono (fun z hz => p.scalar_coefficients_bound z.1 hz)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPacket
