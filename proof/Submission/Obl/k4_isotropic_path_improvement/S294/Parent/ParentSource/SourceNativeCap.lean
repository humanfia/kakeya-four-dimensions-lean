-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.SourceNativeCap, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/SourceNativeCap.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/SourceNativeCap.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/SourceNativeCap.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.NativeCapAssembly
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Problem

/-! # Pure caps from the exact original source problem -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open scoped ENNReal

/-- The original source's spatial bound and density law supply the native
signal cap in a fixed old packet's full reference units. The only density
ceiling is on the original source density evaluated at the actual event. -/
theorem source_native_signal_cap_in_old_units
    {d : Native.ProblemData} (hd : d.Valid) {k : ℕ} {p : Native.PathData (d.W k)}
    {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (b : Fin p.C) (r' : ℝ) (hr' : 0 ≤ r') (hr'L : r' ≤ d.L)
    (hscale : δ (d.N k) r' ≤ δ (d.N k) (p.r (p.lev b)))
    (ρ : Measure Event) (hρ : ρ ≤ d.μ k (p.γ b)) (M : ENNReal) (z : ℝ)
    (hF : ∀ᵐ q ∂ρ, q ∈ p.F b)
    (hband : ∀ᵐ q ∂ρ, |MvPolynomial.eval (x q.1 q.2) (p.R b) - z| ≤
      max p.κ (d.K k) * δ (d.N k) r')
    (htypical : ∀ᵐ q ∂ρ, d.g k (p.γ b) r'
      (obs (d.B k (p.γ b)) (δ (d.N k) r') q) ≤ M) :
    (d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹))⁻¹ •
      ρ.map (fun q => (nativeOldBaseFrame p b).obsBase
        (obs (d.B k (p.γ b)) (δ (d.N k) r') q).1) ≤
      ((M * ENNReal.ofReal (64 * (max p.κ (d.K k)) ^ 2)) *
        ENNReal.ofReal (p.κ * d.N k ^ d.f (p.r (p.lev b)))) • volume := by
  have hNk : 0 < d.N k := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hd.1 k)
  have hraw : path (d.N k) d.L (d.W k) (d.ω k) (d.ν k) (d.E k) (d.B k)
      d.f κ₁ m s δ₀ Mp Dp σ p.r p.T p.nw p.κ p.C p.lev p.par p.γ p.j
      p.c p.u p.Q p.R p.A p.F p.lst := hp
  have hB : 0 < d.B k (p.γ b) := by
    rcases hd with ⟨_, _, _, _, _, _, _, _, hformat, _⟩
    obtain ⟨M, D, hformat⟩ := hformat
    exact ((hformat k).2.2.2.1 (p.γ b)).2.1
  have hg := hd.2.2.2.2.2.2.2.2.2.1 k (p.γ b) r' hr' hr'L
  have hfull := (Measure.quasiMeasurePreserving_fst
    (μ := d.ν k (p.γ b)) (ν := (volume : Measure ℝ))).ae (hd.native_bounds k (p.γ b))
  have hρfull : ρ ≤ (d.ν k (p.γ b)).prod volume := hρ.trans Measure.restrict_le_self
  have hy : ∀ᵐ q ∂ρ, ‖y q.1 q.2‖ ≤ max p.κ (d.K k) := by
    filter_upwards [(ae_mono hρfull) hfull, hF] with q hq hqF
    have ht := path_packet_time_unit hraw b hqF
    exact ((le_add_of_nonneg_right (norm_nonneg (v q.1))).trans (hq q.2 ht)).trans
      (le_max_right _ _)
  exact original_native_signal_cap_in_old_packet_units hp hNk b (le_max_left _ _) hB
    (by unfold δ; positivity) hscale ρ hρ (d.g k (p.γ b) r') hg.1 hg.2 M z hF hy
    hband htypical

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
