-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Analytic.OriginalJetNorming, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Analytic/OriginalJetNorming.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Analytic/OriginalJetNorming.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 7287edefaa58;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Analytic/OriginalJetNorming.lean.
-- Only the source value-norming declarations used here are retained; earlier provenance is preserved.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.SampledBranch
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic.RobustTests

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

open MeasureTheory Set Metric
open scoped ENNReal

noncomputable section

/-- An original positive-mass source and a continuous base cap supply the
real set size in the frozen dense-jet bound. -/
theorem original_dense_jet_bound
    {D J : ℕ} (hjets : DenseJetBound D J)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → Base)
    (E : Set Base) (hE : MeasurableSet E) (hEball : E ⊆ closedBall 0 1)
    {A β ε : ℝ} (hA : 2 ≤ A) (hβ : 0 < β) (hε : 0 ≤ ε)
    (hmass : ENNReal.ofReal (β / A) ≤ μ univ)
    (hcap : ∀ U : Set Base, MeasurableSet U → μ (Z ⁻¹' U) ≤ ENNReal.ofReal β * volume U)
    (hsupp : ∀ᵐ p ∂μ, Z p ∈ E)
    (g : Base → ℝ) (hg : HasRealExtension D g) (hsmall : ∀ x ∈ E, |g x| ≤ ε) :
    ∀ j : ℕ, j ≤ 6 → ∀ x ∈ closedBall (0 : Base) 2,
      ‖iteratedFDeriv ℝ j g x‖ ≤ A ^ J * ε := by
  have hsource : μ (Z ⁻¹' E) = μ univ := by
    apply measure_congr
    filter_upwards [hsupp] with p hp
    exact propext (iff_true_intro hp)
  have hvolume : ENNReal.ofReal A⁻¹ ≤ volume E := by
    apply (ENNReal.mul_le_mul_iff_left (by simpa only [ne_eq, ENNReal.ofReal_eq_zero] using hβ.not_ge)
      ENNReal.ofReal_ne_top).mp
    calc
      ENNReal.ofReal A⁻¹ * ENNReal.ofReal β = ENNReal.ofReal (β / A) := by
        rw [mul_comm, ← ENNReal.ofReal_mul hβ.le, div_eq_mul_inv]
      _ ≤ μ univ := hmass
      _ = μ (Z ⁻¹' E) := hsource.symm
      _ ≤ ENNReal.ofReal β * volume E := hcap E hE
      _ = volume E * ENNReal.ofReal β := mul_comm _ _
  exact (hjets A hA g hg).1 E ε hE hEball hvolume hε hsmall


end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
