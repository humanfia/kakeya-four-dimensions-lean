-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.FiniteStates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/FiniteStates.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Generalized from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FrozenFiniteStates.lean.
The bounded physical model replaces the old chart signal.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenFiniteStates.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.StripFilling
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Basic
import Submission.Lib.K4ContinuousPlanks.Discretization


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set

noncomputable section

/-- Bounded native coefficients bound the actual original physical
coordinates throughout the packet's full unit time interval. -/
theorem physical_coordinates_bound (p : PhysicalModel) (hκ : 1 ≤ p.slack)
    (z : Ev) (hz : z ∈ p.event) (j : Fin 4) :
    |originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2 j| ≤
      51 * p.slack := by
  have ht := (p.event_unit_time hz).2
  have hc := p.scalar_coefficients_bound z.1 (p.event_assignment z hz)
  rw [p.physical_scalar_coord]
  fin_cases j
  · change |z.2| ≤ _
    rw [abs_of_nonneg ht.1]
    linarith [ht.2]
  · change |Jets2.zy (p.scalarCoefficients z.1) z.2 0| ≤ _
    linarith [Jets2.abs_zy_le hc ht 0]
  · change |Jets2.zy (p.scalarCoefficients z.1) z.2 1| ≤ _
    linarith [Jets2.abs_zy_le hc ht 1]
  · change |Jets2.zx (p.scalarCoefficients z.1) z.2| ≤ _
    exact (Jets2.abs_zx_le hc ht).trans_eq (by ring)

/-- The finite ORIGINAL fine-state carrier is constructed from the
actual frozen chart. It requires no finite trajectory discretization. -/
theorem finite_physical_state_image (p : PhysicalModel) (hκ : 1 ≤ p.slack)
    {E : Set Ev} (hEp : E ⊆ p.event) {b : ℝ} (hb : 0 < b) :
    (p.physicalState b '' E).Finite := by
  have hf := Submission.Lib.K4ContinuousPlanks.finite_range_floor_code
    (fun z : E => originalPhysicalCoordinates (p.signal z.val.1) (p.position z.val.1)
      (p.velocity z.val.1) z.val.2) (51 * p.slack)
    (fun z j => p.physical_coordinates_bound hκ z.val (hEp z.property) j) hb
  apply hf.subset
  rintro q ⟨z,hz,rfl⟩
  exact ⟨⟨z,hz⟩,rfl⟩

theorem exists_original_fine_state_carrier (p : PhysicalModel) (hκ : 1 ≤ p.slack)
    {E : Set Ev} (hEp : E ⊆ p.event) {b : ℝ} (hb : 0 < b) :
    ∃ F : Finset (Fin 4 → ℤ), ∀ z ∈ E, p.physicalState b z ∈ F := by
  let hf := p.finite_physical_state_image hκ hEp hb
  exact ⟨hf.toFinset, fun z hz => hf.mem_toFinset.mpr ⟨z,hz,rfl⟩⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
