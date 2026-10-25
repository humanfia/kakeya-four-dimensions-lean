-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PureGridCeiling, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PureGridCeiling.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PureGridCeiling.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PureGridCeiling.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Problem
import Submission.Lib.K4ChartLifting.NormCompare

/-! A finite fixed pure-density grid controls ANY actual path depth. The
comparison uses the original dyadic observation laws and profile Lipschitz
bound. It costs only the requested test spacing, with no fixed delta0 loss. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal

theorem ProblemData.Valid.pure_density_antitone {d : ProblemData} (hd : d.Valid)
    (k : ℕ) (w : Fin (d.W k)) {r r' : ℝ}
    (hr : 0 ≤ r) (hrr' : r ≤ r') (hr'L : r' ≤ d.L) :
    ∀ᵐ q ∂d.μ k w,
      d.g k w r' (obs (d.B k w) (δ (d.N k) r') q) ≤
        d.g k w r (obs (d.B k w) (δ (d.N k) r) q) := by
  have hg := hd.2.2.2.2.2.2.2.2.2.1 k w r hr (hrr'.trans hr'L)
  have hg' := hd.2.2.2.2.2.2.2.2.2.1 k w r' (hr.trans hrr') hr'L
  exact Submission.Lib.K4ChartLifting.density_depth_le (d.μ k w) (d.B k w)
    ((by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)) hrr' _ _ hg.1 hg'.1 hg.2 hg'.2

/-- Every submeasure of the original law inherits the fixed-grid upper tests
at all depths, up to its arbitrary test spacing. -/
theorem ProblemData.Valid.pure_ceiling_of_lower_tests {I : Type*}
    {d : ProblemData} (hd : d.Valid) (k : ℕ) (w : Fin (d.W k))
    (ρ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hρ : ρ ≤ d.μ k w)
    (depths : I → ℝ) (hdepth : ∀ i, 0 ≤ depths i ∧ depths i ≤ d.L)
    (τ ε : ℝ)
    (htests : ∀ i, ∀ᵐ q ∂ρ,
      d.g k w (depths i) (obs (d.B k w) (δ (d.N k) (depths i)) q) ≤
        ENNReal.ofReal (d.N k ^ (-d.f (depths i) + τ)))
    (hgrid : ∀ r : ℝ, 0 ≤ r → r ≤ d.L → ∃ i, depths i ≤ r ∧ r - depths i ≤ ε)
    {r : ℝ} (hr : 0 ≤ r) (hrL : r ≤ d.L) :
    ∀ᵐ q ∂ρ, d.g k w r (obs (d.B k w) (δ (d.N k) r) q) ≤
      ENNReal.ofReal (d.N k ^ (-d.f r + τ + ε)) := by
  obtain ⟨i, hir, hgap⟩ := hgrid r hr hrL
  have hmono := (ae_mono hρ) (hd.pure_density_antitone k w (hdepth i).1 hir hrL)
  have hprofile : d.f r - d.f (depths i) ≤ r - depths i := by
    rcases hd with ⟨_, _, _, _, _, _, _, _, _, _, _, hf, _⟩
    exact (hf _ _ (hdepth i).1 hir hrL).2
  have hpow : ENNReal.ofReal (d.N k ^ (-d.f (depths i) + τ)) ≤
      ENNReal.ofReal (d.N k ^ (-d.f r + τ + ε)) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_exponent_le ((by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k))
    linarith
  filter_upwards [hmono, htests i] with q hq hqt
  exact hq.trans (hqt.trans hpow)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
