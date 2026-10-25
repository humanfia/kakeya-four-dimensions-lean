-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.OccupationMarginals, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/OccupationMarginals.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/OccupationMarginals.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 5bf2ec7212f0;
-- source Submission/Obl/k4_isotropic_path_improvement/OccupationMarginals.lean.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.Incidence
import Submission.Lib.K4Homogenization.RetainedDuration

/-!
Cell occupation laws retain the original trajectory prior. Their densities
are the weighted time durations, and a cell-duration ceiling is exactly
the measure domination needed for the physical velocity-graph estimate.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity


open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4Homogenization
open Submission.Obl.k4_mk_grid_transfer

noncomputable section

variable {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]

/-- The trajectory marginal counts weighted occupation, without normalizing
by the selected mass. -/
def occupationMarginal (ν : Measure X) (τ : Measure T) (G : X × T → ℝ≥0∞) : Measure X :=
  ((ν.prod τ).withDensity G).map Prod.fst

/-- The original prior density of occupation is precisely the duration. -/
theorem occupationMarginal_eq (ν : Measure X) [SFinite ν] (τ : Measure T) [SFinite τ]
    {G : X × T → ℝ≥0∞} (hG : Measurable G) :
    occupationMarginal ν τ G = ν.withDensity (incidenceDuration τ G univ) := by
  apply Measure.ext
  intro S hS
  rw [occupationMarginal, Measure.map_apply measurable_fst hS]
  have hpre : Prod.fst ⁻¹' S = S ×ˢ (univ : Set T) := by ext p; simp
  rw [hpre, duration_rectangle_mass ν τ hG hS MeasurableSet.univ,
    withDensity_apply _ hS]

/-- A per-trajectory cell-duration bound gives domination by the same prior. -/
theorem occupationMarginal_le (ν : Measure X) [SFinite ν] (τ : Measure T) [SFinite τ]
    {G : X × T → ℝ≥0∞} (hG : Measurable G) (b : ℝ≥0∞)
    (hbound : ∀ᵐ x ∂ν, incidenceDuration τ G univ x ≤ b) :
    occupationMarginal ν τ G ≤ b • ν := by
  rw [occupationMarginal_eq ν τ hG]
  simpa only [withDensity_const] using withDensity_mono hbound

theorem occupationMarginal_finite (ν : Measure X) [IsFiniteMeasure ν]
    (τ : Measure T) [SFinite τ] {G : X × T → ℝ≥0∞} (hG : Measurable G)
    (b : ℝ) (hbound : ∀ᵐ x ∂ν, incidenceDuration τ G univ x ≤ ENNReal.ofReal b) :
    IsFiniteMeasure (occupationMarginal ν τ G) := by
  constructor
  exact ((occupationMarginal_le ν τ hG _ hbound) univ).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν univ))

theorem occupationMarginal_real_le (ν : Measure X) [IsFiniteMeasure ν]
    (τ : Measure T) [SFinite τ] {G : X × T → ℝ≥0∞} (hG : Measurable G)
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ᵐ x ∂ν, incidenceDuration τ G univ x ≤ ENNReal.ofReal b)
    (S : Set X) :
    (occupationMarginal ν τ G).real S ≤ b * ν.real S := by
  have h := occupationMarginal_le ν τ hG (ENNReal.ofReal b) hbound
  have h' := ENNReal.toReal_mono
    (show (ENNReal.ofReal b • ν) S ≠ ∞ by
      simpa only [Measure.smul_apply, smul_eq_mul] using
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν S)) (h S)
  simpa only [measureReal_def, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hb] using h'

/-- The total occupation remains the full original incidence mass. -/
theorem occupationMarginal_univ (ν : Measure X) (τ : Measure T)
    (G : X × T → ℝ≥0∞) :
    occupationMarginal ν τ G univ = (ν.prod τ).withDensity G univ := by
  simp [occupationMarginal, Measure.map_apply measurable_fst MeasurableSet.univ]

/-- If every positive-weight incidence uses a trajectory in `S`, the
occupation marginal is supported on that same trajectory event. -/
theorem occupationMarginal_support (ν : Measure X) [SFinite ν]
    (τ : Measure T) [SFinite τ] {G : X × T → ℝ≥0∞} (hG : Measurable G)
    {S : Set X} (hS : MeasurableSet S)
    (hsupp : ∀ x t, G (x, t) ≠ 0 → x ∈ S) :
    occupationMarginal ν τ G Sᶜ = 0 := by
  rw [occupationMarginal_eq ν τ hG, withDensity_apply _ hS.compl]
  apply setLIntegral_eq_zero hS.compl
  intro x hx
  unfold incidenceDuration
  have hxG : (fun t => G (x, t)) = 0 := by
    funext t
    exact not_ne_iff.mp (fun h => hx (hsupp x t h))
  rw [hxG]
  exact lintegral_zero_fun

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
