-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.TrajectoryBreadth, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/TrajectoryBreadth.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/TrajectoryBreadth.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 5bf2ec7212f0;
-- source Submission/Obl/k4_isotropic_path_improvement/TrajectoryBreadth.lean.
import Mathlib

/-!
Breadth of a time-dependent incidence law transfers to its unchanged
trajectory marginal when directions are uniformly close almost everywhere.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity


open MeasureTheory Set

noncomputable section

/-- Transfer incidence breadth to a fixed direction attached to each
trajectory, with only the additive direction error in the threshold. -/
theorem map_fst_breadth_transfer
    {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (μ : Measure (X × T)) [IsFiniteMeasure μ]
    (u : X × T → EuclideanSpace ℝ (Fin 4)) (e : X → EuclideanSpace ℝ (Fin 4))
    (he : Measurable e) (ρ ε c : ℝ)
    (hclose : ∀ᵐ p ∂μ, ‖u p - e p.1‖ ≤ ε)
    (hbroad : ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)), Module.finrank ℝ V < 4 →
      c * μ.real univ ≤ μ.real {p | ρ ≤ Metric.infDist (u p) (V : Set _)}) :
    ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)), Module.finrank ℝ V < 4 →
      c * (μ.map Prod.fst).real univ ≤
        (μ.map Prod.fst).real {x | ρ - ε ≤ Metric.infDist (e x) (V : Set _)} := by
  intro V hV
  have hset : MeasurableSet {x | ρ - ε ≤ Metric.infDist (e x) (V : Set _)} :=
    measurableSet_le measurable_const ((Metric.continuous_infDist_pt _).measurable.comp he)
  have hsub : {p | ρ ≤ Metric.infDist (u p) (V : Set _)} ≤ᵐ[μ]
      Prod.fst ⁻¹' {x | ρ - ε ≤ Metric.infDist (e x) (V : Set _)} := by
    filter_upwards [hclose] with p hp htail
    have h := Metric.infDist_le_infDist_add_dist (x := u p) (y := e p.1) (s := (V : Set _))
    rw [dist_eq_norm] at h
    change ρ - ε ≤ Metric.infDist (e p.1) (V : Set _)
    linarith
  have hmono := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
  have hmass : (μ.map Prod.fst).real univ = μ.real univ := by
    rw [map_measureReal_apply measurable_fst MeasurableSet.univ]
    simp only [preimage_univ]
  rw [hmass]
  refine (hbroad V hV).trans ?_
  rw [map_measureReal_apply measurable_fst hset]
  exact hmono

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
