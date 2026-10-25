-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.SourceNativeCubeCap, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/SourceNativeCubeCap.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/SourceNativeCubeCap.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/SourceNativeCubeCap.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/SourceNativeCubeCap.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceNativeCap
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketNativeCube

/-! # The actual original-law cap required by native branch preparation -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory
open Analytic
open scoped ENNReal

/-- An original fine-entry submeasure has a unit-base native cap in FULL
original packet units. Its original source density is evaluated at the
actual finer observation; the denominator never depends on the entry. -/
theorem source_native_cube_cap
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
    let α := (d.ν k (p.γ b) (p.A b) *
      ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹))⁻¹
    let C := ((M * ENNReal.ofReal (64 * (max p.κ (d.K k)) ^ 2)) *
      ENNReal.ofReal (p.κ * d.N k ^ d.f (p.r (p.lev b)))) *
        ENNReal.ofReal (36 * p.κ ^ 2)
    (α • ρ).map (fun q => WithLp.toLp 2
      (fun j : Fin 3 => packetNativeCubePoint (d.N k) (d.B k) p b q j.castSucc)) ≤ C • volume := by
  dsimp only
  let α := (d.ν k (p.γ b) (p.A b) *
    ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹))⁻¹
  let C₀ := (M * ENNReal.ofReal (64 * (max p.κ (d.K k)) ^ 2)) *
    ENNReal.ofReal (p.κ * d.N k ^ d.f (p.r (p.lev b)))
  have hcap : (α • ρ).map (packetBase p b) ≤ C₀ • volume := by
    rw [Measure.map_smul α (measurable_packetBase p b).aemeasurable]
    exact source_native_signal_cap_in_old_units hd hp b r' hr' hr'L hscale
      ρ hρ M z hF hband htypical
  have hc := original_native_cube_base_cap (α • ρ) (packetBase p b)
    (measurable_packetBase p b) (show 0 < 3 * p.κ by linarith [hp.1]) C₀ hcap
  have hfun : (fun q => WithLp.toLp 2
      (fun j : Fin 3 => packetNativeCubePoint (d.N k) (d.B k) p b q j.castSucc)) =
      nativeCubeBase (3 * p.κ) ∘ packetBase p b := by
    funext q
    exact packetNativeCube_base_eq _ _ _ _ _
  rw [hfun]
  simpa only [show 4 * (3 * p.κ) ^ 2 = 36 * p.κ ^ 2 by ring] using hc

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
