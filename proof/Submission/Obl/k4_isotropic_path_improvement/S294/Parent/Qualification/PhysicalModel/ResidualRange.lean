-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.ResidualRange, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/ResidualRange.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Generalized from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FrozenResidualRange.lean.
The bounded physical model replaces the old chart signal.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenResidualRange.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.StripFilling
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ParameterZoom


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set
open scoped BigOperators

noncomputable section

/-- The original graph error is exactly the scalar residual error for
the actual seven native coefficients and the actual tangential velocity. -/
theorem original_graph_error_scalar (p : PhysicalModel) (l : Ln) (t : ℝ)
    (G : Fin 3 → ℝ) (error : ℝ)
    (hgraph : |(p.signal l).derivative.eval t - ∑ j, G j * p.velocity l j| ≤ error) :
    |p.scalarCoefficients l 1 + 2 * p.scalarCoefficients l 2 * t - G 0 -
      (fun i : Fin 2 => G i.succ) ⬝ᵥ Jets2.zv (p.scalarCoefficients l)| ≤ error := by
  have hid : p.scalarCoefficients l 1 + 2 * p.scalarCoefficients l 2 * t - G 0 -
      (fun i : Fin 2 => G i.succ) ⬝ᵥ Jets2.zv (p.scalarCoefficients l) =
      (p.signal l).derivative.eval t - ∑ j, G j * p.velocity l j := by
    rw [p.scalar_x_derivative]
    simp [Jets2.zv,scalarCoefficients,velocity,dotProduct,Fin.sum_univ_two,Fin.sum_univ_three]
    ring
  rw [hid]
  exact hgraph

theorem time_gap_of_original_state (p : PhysicalModel) {b : ℝ} (hb : 0 < b)
    (z z' : Ev) (hstate : p.physicalState b z = p.physicalState b z') :
    |z.2-z'.2| ≤ b := by
  have ht := congrFun hstate 0
  change ⌊originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2 0 / b⌋ =
    ⌊originalPhysicalCoordinates (p.signal z'.1) (p.position z'.1) (p.velocity z'.1) z'.2 0 / b⌋ at ht
  rw [originalPhysicalCoordinates_time _ _ _ rfl (p.velocity_time z.1),
    originalPhysicalCoordinates_time _ _ _ rfl (p.velocity_time z'.1)] at ht
  exact (Submission.Lib.K4QuadraticSheets.abs_sub_lt_of_floor_eq hb ht).le

/-- Actual residual oscillation on one original fine state in one
full parameter world. The only errors are the original graph error,
the row fit and the actual original fine time-cell diameter. -/
theorem original_fine_state_residual_range (p : PhysicalModel) (E : Set Ev)
    (G : (Fin 4 → ℤ) → Fin 3 → ℝ) (center : Fin 7 → ℝ) (F : ℝ → Fin 2 → ℝ)
    (b ρ K η error : ℝ) (hb : 0 < b) (hρ : 0 < ρ) (hK : 0 ≤ K) (hη : 0 ≤ η)
    (hcenter : |center 2| ≤ K)
    (hdiam : ∀ z ∈ E, ∀ i, |p.scalarCoefficients z.1 i - center i| ≤ ρ)
    (hrow : ∀ z ∈ E, ∀ i : Fin 2, |G (p.physicalState b z) i.succ - F z.2 i| ≤ η)
    (hgraph : ∀ z ∈ E,
      |(p.signal z.1).derivative.eval z.2 - ∑ j, G (p.physicalState b z) j * p.velocity z.1 j| ≤ error) :
    ∀ z ∈ E, ∀ z' ∈ E, p.physicalState b z = p.physicalState b z' →
      |Jets2.zR F (Jets2.zoomCoefficients ρ center (p.scalarCoefficients z.1)) z.2 -
        Jets2.zR F (Jets2.zoomCoefficients ρ center (p.scalarCoefficients z'.1)) z'.2| ≤
          (2 * (error + 2 * η * ρ) + 2 * K * b) / ρ := by
  intro z hz z' hz' hstate
  have hvel (w : Ev) (hw : w ∈ E) (i : Fin 2) :
      |Jets2.zv (p.scalarCoefficients w.1) i - Jets2.zv center i| ≤ ρ := by
    fin_cases i
    · exact hdiam w hw 4
    · exact hdiam w hw 6
  have hrow' := hrow z' hz'
  have hgraph' := p.original_graph_error_scalar z'.1 z'.2 (G (p.physicalState b z')) error (hgraph z' hz')
  rw [← hstate] at hrow' hgraph'
  have hh := Jets2.zoom_residual_original_state_range ρ hρ center
    (p.scalarCoefficients z.1) (p.scalarCoefficients z'.1) F
    (G (p.physicalState b z) 0) (fun i : Fin 2 => G (p.physicalState b z) i.succ)
    z.2 z'.2 η ρ error hη hρ.le (hrow z hz) hrow' (hvel z hz) (hvel z' hz')
    (p.original_graph_error_scalar z.1 z.2 _ error (hgraph z hz)) hgraph'
  apply hh.trans
  apply div_le_div_of_nonneg_right _ hρ.le
  have htime := p.time_gap_of_original_state hb z z' hstate
  have hc := mul_le_mul hcenter htime (abs_nonneg _) hK
  nlinarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
