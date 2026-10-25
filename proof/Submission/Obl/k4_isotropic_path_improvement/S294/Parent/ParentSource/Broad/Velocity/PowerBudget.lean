-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.PowerBudget, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/PowerBudget.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/PowerBudget.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.Incidence
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.SupportGap

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity

open MeasureTheory Set
open scoped BigOperators
open Submission.Obl.k4_mk_grid_transfer

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An anisotropic support count gives the same hidden-scale saving for
every sufficiently fine base mesh. -/
theorem anisotropic_broad_incidence_mass_power_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω],
      ∀ (m : ℕ) (z : Fin m → Fin 4 → ℤ), Function.Injective z →
      ∀ (ν : Measure Ω) [IsFiniteMeasure ν] (laws : Fin m → Measure Ω)
        [∀ q, IsFiniteMeasure (laws q)] (anchor e : Ω → Space),
      Measurable e → (∀ x, ‖e x‖ = 1) →
      ∀ ρ c K p b M d : ℝ, 0 < ρ → 0 ≤ c → 0 < K → 0 < p → p ≤ b →
      (∀ q : Fin m, MeasurableSet {x |
        latticePoint (z q) ∈ lineTube 3 (anchor x) (heightUnit (p / b) (e x))}) →
      (∀ q E, (laws q).real E ≤ (K * p) * ν.real E) →
      (∀ q : Fin m, laws q {x |
        latticePoint (z q) ∉ lineTube 3 (anchor x) (heightUnit (p / b) (e x))} = 0) →
      (∀ q : Fin m, ∀ V : Submodule ℝ Space, Module.finrank ℝ V < 4 →
        c * (laws q).real univ ≤ (laws q).real {x | ρ ≤ Metric.infDist (e x) (V : Set _)}) →
      ν.real univ ≤ K * M / b ^ ((2 : ℝ) / 3) →
      (m : ℝ) ≤ K * (b ^ ((2 : ℝ) / 3) / p) ^ 3 * (b ^ ((2 : ℝ) / 3) / b) ^ d →
      (c * ρ / 2) ^ 4 * (∑ q : Fin m, (laws q).real univ) ^ 4 ≤
        256 * C ^ 3 * K ^ 9 * M ^ 4 * b ^ ((1 - d) / 3) := by
  obtain ⟨C, hC, hbudget⟩ := anisotropic_incidence_line_law_support_budget
  refine ⟨C, hC, ?_⟩
  intro Ω instΩ m z hz ν hν laws hlaws anchor e he hunit ρ c K p b M d
    hρ hc hK hp hpb hsets hdom hsupp hbroad hprior hcount
  have hb : 0 < b := hp.trans_le hpb
  have h := hbudget m z hz ν laws anchor e (p / b) (div_pos hp hb)
    ((div_le_one hb).mpr hpb) he hunit hsets ρ c (K * p) hρ hc (mul_pos hK hp)
    hdom hsupp hbroad
  exact anisotropic_incidence_mass_power_bound_two_thirds measureReal_nonneg hC.le hK hp hb
    h hprior hcount

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
