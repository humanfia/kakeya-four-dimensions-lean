-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.OccupationBudget, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/OccupationBudget.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/OccupationBudget.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 5bf2ec7212f0;
-- source Submission/Obl/k4_isotropic_path_improvement/OccupationMarginals.lean.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.PowerBudget
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.OccupationMarginals

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4Homogenization
open Submission.Obl.k4_mk_grid_transfer

noncomputable section

variable {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]

/-- The support obstruction stated directly for original weighted incidence
laws. All cell marginals use the same unchanged trajectory prior. -/
theorem anisotropic_broad_occupation_mass_power_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : Type*} {T : Type*} [MeasurableSpace X] [MeasurableSpace T],
      ∀ (m : ℕ) (z : Fin m → Fin 4 → ℤ), Function.Injective z →
      ∀ (ν : Measure X) [IsFiniteMeasure ν] (τ : Measure T) [SFinite τ]
        (F : Fin m → X × T → ℝ≥0∞) (_hF : ∀ q, Measurable (F q))
        (a e : X → EuclideanSpace ℝ (Fin 4)),
      Measurable e → (∀ x, ‖e x‖ = 1) →
      ∀ ρ c K p b M d : ℝ, 0 < ρ → 0 ≤ c → 0 < K → 0 < p → p ≤ b →
      (∀ q : Fin m, MeasurableSet {x | latticePoint (z q) ∈ lineTube 3 (a x) (heightUnit (p / b) (e x))}) →
      (∀ q, ∀ᵐ x ∂ν, incidenceDuration τ (F q) univ x ≤ ENNReal.ofReal (K * p)) →
      (∀ q x t, F q (x, t) ≠ 0 → latticePoint (z q) ∈ lineTube 3 (a x) (heightUnit (p / b) (e x))) →
      (∀ q : Fin m, ∀ V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)), Module.finrank ℝ V < 4 →
        c * (occupationMarginal ν τ (F q)).real univ ≤
          (occupationMarginal ν τ (F q)).real {x | ρ ≤ Metric.infDist (e x) (V : Set _)}) →
      ν.real univ ≤ K * M / b ^ ((2 : ℝ) / 3) →
      (m : ℝ) ≤ K * (b ^ ((2 : ℝ) / 3) / p) ^ 3 * (b ^ ((2 : ℝ) / 3) / b) ^ d →
      (c * ρ / 2) ^ 4 * (∑ q : Fin m, ((ν.prod τ).withDensity (F q)).real univ) ^ 4 ≤
        256 * C ^ 3 * K ^ 9 * M ^ 4 * b ^ ((1 - d) / 3) := by
  obtain ⟨C, hC, hbudget⟩ := anisotropic_broad_incidence_mass_power_bound
  refine ⟨C, hC, ?_⟩
  intro X T instX instT m z hz ν hν τ hτ F hF a e he hunit ρ c K p b M d
    hρ hc hK hp hpb hsets hduration hsupp hbroad hprior hcount
  let laws (q : Fin m) := occupationMarginal ν τ (F q)
  have (q : Fin m) : IsFiniteMeasure (laws q) :=
    occupationMarginal_finite ν τ (hF q) (K * p) (hduration q)
  have h := hbudget m z hz ν laws a e he hunit ρ c K p b M d hρ hc hK hp hpb hsets
    (fun q E => occupationMarginal_real_le ν τ (hF q) (K * p) (by positivity) (hduration q) E)
    (fun q => occupationMarginal_support ν τ (hF q) (hsets q) (hsupp q))
    hbroad hprior hcount
  simpa only [laws, measureReal_def, occupationMarginal_univ] using h

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
