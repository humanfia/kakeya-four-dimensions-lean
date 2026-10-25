-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.FrozenPacketQuadratics, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/FrozenPacketQuadratics.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/FrozenPacketQuadratics.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 38d075b9;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenPacketQuadratics.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPacketGeometry
import Submission.Lib.K4ProjectedGroups.LineSignal
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry.QuadraticTangents
import Submission.Obl.k4_scalar_coefficient_clustering.Geometry
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

/-!
Canonical quadratic data for the actual normalized frozen packet.
Adapted from this LOT tree, o204, session x0747, branch x0747,
commit b5bc2d88,
`Submission/Obl/k4_uniform_sampled_isotropic_branches/PacketQuadratics.lean`.
The coefficient and quadratic theorems are imported from the accepted
K4ProjectedGroups.LineSignal contribution (o200, x0701); this lighter
import avoids the unrelated native atlas construction in o160.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPacket

open Set MeasureTheory

noncomputable section

def coefficients (p : FrozenPacket) (l : Line) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![
    Submission.Lib.K4ProjectedGroups.sc0 p.test (p.line l).2,
    Submission.Lib.K4ProjectedGroups.sc1 p.test (p.line l).2,
    Submission.Lib.K4ProjectedGroups.sc2 p.test (p.line l).2]

theorem measurable_coefficients (p : FrozenPacket) : Measurable p.coefficients := by
  have hc : Measurable (fun l : Line => (p.line l).2) := measurable_snd.comp p.measurable_line
  unfold coefficients
  apply (PiLp.volume_preserving_toLp (Fin 3)).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · exact (Submission.Lib.K4ProjectedGroups.continuous_sc0 p.test).measurable.comp hc
  · exact (Submission.Lib.K4ProjectedGroups.continuous_sc1 p.test).measurable.comp hc
  · exact (Submission.Lib.K4ProjectedGroups.continuous_sc2 p.test).measurable.comp hc

theorem signal_quadratic (p : FrozenPacket) (l : Line) :
    Submission.Obl.k4_eligibility_sign_description.Quadratic (p.signalValue l) :=
  Submission.Lib.K4ProjectedGroups.sig_quadratic p.test_degree (p.line l).2

theorem coefficient_identity (p : FrozenPacket) (l : Line) (t : ℝ) :
    p.signalValue l t = p.coefficients l 2 * t ^ 2 +
      p.coefficients l 1 * t + p.coefficients l 0 := by
  have h := Submission.Lib.K4ProjectedGroups.sig_eq p.test_degree (p.line l).2 t
  calc
    _ = p.coefficients l 0 + t * p.coefficients l 1 + t ^ 2 * p.coefficients l 2 := h
    _ = _ := by ring

theorem coefficients_bound (p : FrozenPacket) (l : Line) (hl : l ∈ p.assigned) :
    ‖p.coefficients l‖ ≤ 17 * p.slack := by
  have h : ∀ t ∈ Icc (0 : ℝ) 1,
      |Submission.Lib.K4ProjectedGroups.sig p.test (p.line l).2 t| ≤ p.slack :=
    fun t ht => (p.native_bounds l hl t ht).2.1
  have h0 := Submission.Lib.K4ProjectedGroups.abs_sc0_le h
  have h1 := Submission.Lib.K4ProjectedGroups.abs_sc1_le h
  have h2 := Submission.Lib.K4ProjectedGroups.abs_sc2_le h
  apply (Submission.Obl.k4_scalar_coefficient_clustering.coeff_norm_le_abs_add _).trans
  change |Submission.Lib.K4ProjectedGroups.sc0 p.test (p.line l).2| +
    |Submission.Lib.K4ProjectedGroups.sc1 p.test (p.line l).2| +
    |Submission.Lib.K4ProjectedGroups.sc2 p.test (p.line l).2| ≤ _
  linarith

theorem signal_derivative_identity (p : FrozenPacket) (l : Line) (t : ℝ) :
    (p.signal l).derivative.eval t =
      2 * p.coefficients l 2 * t + p.coefficients l 1 := by
  have h := (p.signal l).hasDerivAt t
  have h' : HasDerivAt (fun s => (p.signal l).eval s)
      (2 * p.coefficients l 2 * t + p.coefficients l 1) t := by
    convert Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry.quadratic_hasDerivAt (p.coefficients l 2) (p.coefficients l 1)
      (p.coefficients l 0) t using 1
    funext s
    exact (p.eval_signal l s).trans (p.coefficient_identity l s)
  exact h.unique h'

theorem signal_derivative_bound (p : FrozenPacket) (l : Line) (hl : l ∈ p.assigned)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |(p.signal l).derivative.eval t| ≤ 51 * p.slack := by
  have hκ : 0 ≤ p.slack :=
    (abs_nonneg (p.signalValue l 0)).trans ((p.native_bounds l hl 0 (by norm_num)).2.1)
  rw [p.signal_derivative_identity]
  have hcoeff (j : Fin 3) : |p.coefficients l j| ≤ 17 * p.slack :=
    (PiLp.norm_apply_le _ _).trans (p.coefficients_bound l hl)
  have ht' : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  calc
    _ ≤ |2 * p.coefficients l 2 * t| + |p.coefficients l 1| := abs_add_le _ _
    _ = 2 * |p.coefficients l 2| * |t| + |p.coefficients l 1| := by norm_num [abs_mul]
    _ ≤ 2 * (17 * p.slack) * 1 + 17 * p.slack := by gcongr <;> exact hcoeff _
    _ = _ := by ring

theorem signal_variation (p : FrozenPacket) (l : Line) (hl : l ∈ p.assigned)
    {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    |p.signalValue l t - p.signalValue l s| ≤ 51 * p.slack * |t - s| := by
  have heq (u : ℝ) : Submission.Obl.k4_scalar_coefficient_clustering.quadratic
      (p.coefficients l) u = p.signalValue l u := by
    rw [p.coefficient_identity]
    dsimp [Submission.Obl.k4_scalar_coefficient_clustering.quadratic]
    ring
  have h := Submission.Obl.k4_scalar_coefficient_clustering.quadratic_time_lipschitz
    (p.coefficients_bound l hl) ht hs
  simpa only [heq, show 3 * (17 * p.slack) = 51 * p.slack by ring] using h

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPacket
