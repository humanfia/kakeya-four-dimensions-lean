-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.PacketStrips, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/PhysicalModel/PacketStrips.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Generalized from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/FrozenPacketStrips.lean.
The bounded quadratic physical model replaces the old chart signal.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenPacketStrips.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.Interface
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ZoomTimeRow
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalStripPriorBudget


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set MeasureTheory

noncomputable section

def physicalIndex : Fin 4 → Fin 4 := ![0, 2, 3, 1]

/-- The strip coordinates are the actual native base followed by the
actual native signal. Scalar-normal coordinates use a fixed permutation. -/
theorem physical_scalar_coord (p : PhysicalModel) (l : Ln) (t : ℝ) (j : Fin 4) :
    originalPhysicalCoordinates (p.signal l) (p.position l) (p.velocity l) t j =
      Jets2.zpos (p.scalarCoefficients l) t (physicalIndex j) := by
  fin_cases j
  · simp [originalPhysicalCoordinates, physicalIndex, Jets2.zpos, position, velocity]
  · change p.position l 1 + p.velocity l 1 * t =
      p.scalarCoefficients l 3 + p.scalarCoefficients l 4 * t
    simp [position, velocity]
  · change p.position l 2 + p.velocity l 2 * t =
      p.scalarCoefficients l 5 + p.scalarCoefficients l 6 * t
    simp [position, velocity]
  · change (p.signal l).eval t = Jets2.zx (p.scalarCoefficients l) t
    exact (p.eval_signal l t).trans (p.scalar_x l t).symm

theorem measurable_physical_coordinates (p : PhysicalModel) :
    Measurable (fun z : Ev =>
      originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2) := by
  have hc : Measurable (fun z : Ev => p.scalarCoefficients z.1) :=
    p.measurable_scalarCoefficients.comp measurable_fst
  have hz : Measurable (fun z : Ev => Jets2.zpos (p.scalarCoefficients z.1) z.2) := by
    unfold Jets2.zpos Jets2.zx Jets2.zy
    fun_prop
  apply measurable_pi_iff.mpr
  intro j
  simp_rw [p.physical_scalar_coord]
  exact (measurable_pi_apply (physicalIndex j)).comp hz

theorem physical_coordinates_variation (p : PhysicalModel) (hκ : 1 ≤ p.slack)
    (l : Ln) (hl : l ∈ p.assigned) (t s : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) (j : Fin 4) :
    |originalPhysicalCoordinates (p.signal l) (p.position l) (p.velocity l) t j -
      originalPhysicalCoordinates (p.signal l) (p.position l) (p.velocity l) s j| ≤
        51 * p.slack * |t - s| := by
  have h := Jets2.original_parameter_world_position_comparison
    (p.scalarCoefficients l) (p.scalarCoefficients l) 0 (17 * p.slack) t s
    (by norm_num) (by linarith) ht hs (by intro i; simp) (p.scalar_coefficients_bound l hl)
  have hj := norm_le_pi_norm
    (Jets2.zpos (p.scalarCoefficients l) t - Jets2.zpos (p.scalarCoefficients l) s) (physicalIndex j)
  change |Jets2.zpos (p.scalarCoefficients l) t (physicalIndex j) -
    Jets2.zpos (p.scalarCoefficients l) s (physicalIndex j)| ≤ _ at hj
  rw [p.physical_scalar_coord, p.physical_scalar_coord]
  exact (hj.trans h).trans_eq (by ring)

theorem velocity_bound (p : PhysicalModel) (hκ : 1 ≤ p.slack)
    (l : Ln) (hl : l ∈ p.assigned) (j : Fin 3) : |p.velocity l j| ≤ 17 * p.slack := by
  have hc := p.scalar_coefficients_bound l hl
  fin_cases j
  · change |(1 : ℝ)| ≤ _
    norm_num
    linarith
  · exact hc 4
  · exact hc 6

/-- The strip analysis always uses the FULL original assignment prior. -/
theorem prior_assignment (p : PhysicalModel) (ν : Measure Ln) :
    ∀ᵐ l ∂p.prior ν, l ∈ p.assigned := by
  apply ae_iff.mpr
  change (p.prior ν) p.assignedᶜ = 0
  rw [p.prior_eq, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply p.measurable_assigned.compl]
  simp

/-- Every geometric line hypothesis for the strip-prior budget is a
consequence of the actual frozen chart, under its original prior. -/
theorem prior_strip_geometry (p : PhysicalModel) (ν : Measure Ln) (hκ : 1 ≤ p.slack) :
    ∀ᵐ l ∂p.prior ν, (p.signal l).natDegree ≤ 2 ∧ p.position l 0 = 0 ∧
      p.velocity l 0 = 1 ∧ (∀ j, |p.velocity l j| ≤ 17 * p.slack) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ∀ j,
        |originalPhysicalCoordinates (p.signal l) (p.position l) (p.velocity l) t j -
          originalPhysicalCoordinates (p.signal l) (p.position l) (p.velocity l) s j| ≤
            (51 * p.slack) * |t - s| := by
  filter_upwards [p.prior_assignment ν] with l hl
  refine ⟨p.signal_degree l, rfl, p.velocity_time l, p.velocity_bound hκ l hl, ?_⟩
  intro t ht s hs j
  exact p.physical_coordinates_variation hκ l hl t s ht hs j

/-- Physical curve speed depends only on four derivative coefficients. -/
theorem physical_coordinates_variation_of_jets (p : PhysicalModel)
    (l : Ln) {H : ℝ} (hH : 1 ≤ H)
    (hjets : |p.scalarCoefficients l 1| ≤ H ∧ |p.scalarCoefficients l 2| ≤ H ∧
      |p.scalarCoefficients l 4| ≤ H ∧ |p.scalarCoefficients l 6| ≤ H)
    (t s : ℝ) (ht : t∈Icc (0:ℝ) 1) (hs : s∈Icc (0:ℝ) 1) (j : Fin 4) :
    |originalPhysicalCoordinates (p.signal l) (p.position l) (p.velocity l) t j-
      originalPhysicalCoordinates (p.signal l) (p.position l) (p.velocity l) s j| ≤
        3*H*|t-s| := by
  have hh := Jets2.original_parameter_world_position_comparison_of_jets
    (p.scalarCoefficients l) (p.scalarCoefficients l) 0 H t s
    (by norm_num) hH ht hs (by intro i; simp) hjets
  rw [p.physical_scalar_coord,p.physical_scalar_coord]
  exact ((norm_le_pi_norm _ (physicalIndex j)).trans hh).trans_eq (by simp)

/-- The complete original prior inherits the four-jet curve and velocity
bounds; no absolute signal intercept enters either constant. -/
theorem prior_strip_geometry_of_jets (p : PhysicalModel) (ν : Measure Ln)
    {H : ℝ} (hH : 1 ≤ H)
    (hjets : ∀ l∈p.assigned, |p.scalarCoefficients l 1| ≤ H ∧
      |p.scalarCoefficients l 2| ≤ H ∧ |p.scalarCoefficients l 4| ≤ H ∧
        |p.scalarCoefficients l 6| ≤ H) :
    ∀ᵐ l ∂p.prior ν, (p.signal l).natDegree ≤ 2 ∧ p.position l 0=0 ∧
      p.velocity l 0=1 ∧ (∀ j, |p.velocity l j| ≤ H) ∧
      ∀ t∈Icc (0:ℝ) 1, ∀ s∈Icc (0:ℝ) 1, ∀ j,
        |originalPhysicalCoordinates (p.signal l) (p.position l) (p.velocity l) t j-
          originalPhysicalCoordinates (p.signal l) (p.position l) (p.velocity l) s j| ≤
            (3*H)*|t-s| := by
  filter_upwards [p.prior_assignment ν] with l hl
  have hj := hjets l hl
  refine ⟨p.signal_degree l,rfl,p.velocity_time l,?_,?_⟩
  · intro j
    fin_cases j
    · change |(1:ℝ)| ≤ H
      simpa only [abs_one] using hH
    · exact hj.2.2.1
    · exact hj.2.2.2
  · intro t ht s hs j
    exact p.physical_coordinates_variation_of_jets l hH hj t s ht hs j

/-- Actual supporting-prior budget in one frozen native packet. All
degree, velocity, measurability, unit-time and curve-variation inputs
come from that packet; only its prepared field comparison remains. -/
theorem strip_support_prior_budget (p : PhysicalModel) (ν : Measure Ln)
    {H : ℝ} (hH : 1 ≤ H)
    (hjets : ∀ l∈p.assigned, |p.scalarCoefficients l 1| ≤ H ∧
      |p.scalarCoefficients l 2| ≤ H ∧ |p.scalarCoefficients l 4| ≤ H ∧
        |p.scalarCoefficients l 6| ≤ H)
    (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (field : Ev → Fin 3 → ℝ)
    {E : Set Ev} (hE : MeasurableSet E) (hEp : E ⊆ p.event)
    (F : Finset ((Fin 4 → ℤ) × ℤ)) (ρ b B error η width : ℝ)
    (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b ≤ ρ) (hB : 0 ≤ B)
    (he : 0 ≤ error) (hη : 0 ≤ η) (hw : 0 < width)
    (D : ℕ) (hD : 1 ≤ D) (hscale : 3 * H ≤ (D : ℝ) * ρ)
    (hrow_bound : ∀ C j, |row C j| ≤ B)
    (hgraph : ∀ z ∈ E,
      |(p.signal z.1).derivative.eval z.2 - ∑ j, field z j * p.velocity z.1 j| ≤ error)
    (hrow : ∀ z ∈ E, ∀ j,
      |field z j - row (roundedPhysicalCode b ρ
        (originalPhysicalCoordinates (p.signal z.1) (p.position z.1) (p.velocity z.1) z.2)) j| ≤ η) :
    (∑ i ∈ F, (p.prior ν) (originalOccupationSupport volume
      (originalStripDensity E (originalStripLabel b ρ width row p.signal p.position p.velocity) i))) ≤
        ENNReal.ofReal (stripVisitBound D ρ b B error η (H) width) * (p.prior ν) univ := by
  apply actual_strip_support_prior_budget (p.prior ν) p.signal p.position p.velocity row field hE F
    (3 * H) ρ b B error η (H) width
    (by linarith) hρ hb hbρ hB he hη (by linarith) hw D hD hscale
    p.measurable_physical_coordinates (p.prior_strip_geometry_of_jets ν hH hjets) hrow_bound
  · intro z hz
    exact (p.event_unit_time (hEp hz)).2
  · exact hgraph
  · exact hrow

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
