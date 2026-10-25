-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.UniformPurePreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/UniformPurePreparation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/UniformPurePreparation.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/UniformPurePreparation.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.BufferedPureTests
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PureDepthGrid
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PureGridCeiling

/-! Original angular preparation with pure ceilings at every actual depth.
Only a finite fixed test grid is deleted. The later submeasure may depend on
the supplied path, entry, core, or value bin, and is never renormalized. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

def PreparedAngularPath.uniformPureCeiling {T : Type*} {d : ProblemData} {k : ℕ}
    {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
    (Q : PreparedAngularPath d k p m H u τ) (ε : ℝ) : Prop :=
  ∀ w (ρ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)), ρ ≤ d.μ k w →
    (∀ᵐ q ∂ρ, q ∈ Q.base w) → ∀ r : ℝ, 0 ≤ r → r ≤ d.L →
    ∀ᵐ q ∂ρ, d.g k w r (obs (d.B k w) (δ (d.N k) r) q) ≤
      ENNReal.ofReal (d.N k ^ (-d.f r + τ + ε))

/-- The original mass buffer and angular references coexist with arbitrary
actual-depth pure ceilings at any requested extra tolerance. -/
theorem ProblemData.Valid.prepare_native_angular_path_uniform_pure {T : Type*} [Fintype T]
    {d : ProblemData} (hd : d.Valid) (κ₁ : ℝ) (m : ℕ) (hm : 0 < m)
    (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) (u : T → ℝ)
    (hu : ∀ t, 0 < u t ∧ u t ≤ d.η * d.L)
    (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ k in atTop, ∀ p : PathData (d.W k),
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ →
      ∀ H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (∀ w, MeasurableSet (H w)) →
      (∀ w, H w ⊆ {q | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ q ∈ p.F b}) →
      ENNReal.ofReal (p.κ⁻¹ / 2) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w) →
      ∃ Q : PreparedAngularPath d k p m H u τ,
        ENNReal.ofReal (11 * p.κ⁻¹ / 32) ≤
          ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Q.residual w) ∧
        Q.uniformPureCeiling ε := by
  obtain ⟨n, hn, depths, hdepth, hgrid⟩ := exists_fixed_lower_depth_grid hd.2.2.2.1 hε
  obtain ⟨σ, hσ, hprep⟩ := hd.prepare_native_angular_path_buffered_pure_tests
    κ₁ m hm s δ₀ Mp Dp depths hdepth u hu τ hτ
  refine ⟨σ, hσ, hprep.mono ?_⟩
  intro k hk p hp H hH hcover hmass
  obtain ⟨Q, htests, hmassQ⟩ := hk p hp H hH hcover hmass
  refine ⟨Q, hmassQ, ?_⟩
  intro w ρ hρ hbase r hr hrL
  apply hd.pure_ceiling_of_lower_tests k w ρ hρ depths hdepth τ ε _ hgrid hr hrL
  intro i
  exact hbase.mono fun q hq => (htests w q hq i).2

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
