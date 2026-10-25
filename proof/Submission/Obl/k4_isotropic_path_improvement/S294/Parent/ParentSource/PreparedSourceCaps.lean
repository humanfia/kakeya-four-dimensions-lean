-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.PreparedSourceCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/PreparedSourceCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/PreparedSourceCaps.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourcePhysicalCap
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.UniformPurePreparation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.CapExponentNumerics

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native
open scoped ENNReal

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ ε : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  (hpure : Q.uniformPureCeiling ε) (hd : d.Valid)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
  (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
    κ₁ m s δ₀ Mp Dp σ)

include hpure hd hp

/-- Every later original submeasure inherits the continuous pure cap at
its actual depth. Its denominator is the unchanged old assignment budget. -/
theorem Native.PreparedAngularPath.native_signal_cap
    (b : Fin p.C) (r' : ℝ) (hr' : 0 ≤ r') (hr'L : r' ≤ d.L)
    (hscale : δ (d.N k) r' ≤ δ (d.N k) (p.r (p.lev b)))
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ b)) (center : ℝ)
    (hbase : ∀ᵐ x ∂μ, x ∈ Q.base (p.γ b))
    (hF : ∀ᵐ x ∂μ, x ∈ p.F b)
    (hband : ∀ᵐ z ∂μ, |MvPolynomial.eval (xp z.1 z.2) (p.R b) - center| ≤
      max p.κ (d.K k) * δ (d.N k) r') :
    (d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹))⁻¹ •
      μ.map (fun x => (nativeOldBaseFrame p b).obsBase
        (obs (d.B k (p.γ b)) (δ (d.N k) r') x).1) ≤
      ((ENNReal.ofReal (d.N k ^ (-d.f r' + τ + ε)) *
        ENNReal.ofReal (64 * (max p.κ (d.K k)) ^ 2)) *
        ENNReal.ofReal (p.κ * d.N k ^ d.f (p.r (p.lev b)))) • volume := by
  exact source_native_signal_cap_in_old_units hd hp b r' hr' hr'L hscale μ hμ _ center
    hF hband (hpure _ μ hμ hbase r' hr' hr'L)

/-- An actual physical cube has the `3+d1` cap, up to the two profile
errors and requested pure-test tolerance, in full original packet units. -/
theorem Native.PreparedAngularPath.physical_cell_cap
    (a : Fin p.C) (r' : ℝ) (hr' : 0 ≤ r') (hr'L : r' ≤ d.L)
    (hscale : δ (d.N k) r' ≤ δ (d.N k) (p.r (p.lev a)))
    {mesh : ℝ} (hmesh : 0 < mesh)
    (hwidth : δ (d.N k) (p.r (p.lev a)) * mesh ≤ δ (d.N k) r')
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ a)) (c : Fin 4 → ℤ)
    (hbase : ∀ᵐ x ∂μ, x ∈ Q.base (p.γ a))
    (hF : ∀ᵐ x ∂μ, x ∈ p.F a)
    (hcell : ∀ᵐ x ∂μ, ∀ j, ⌊packetPhysicalPoint (d.N k) p a x j / mesh⌋ = c j)
    {d₁ f₀ error : ℝ}
    (hprofile : |d.f (p.r (p.lev a)) - f₀ - d₁ * p.r (p.lev a)| ≤ error)
    (hprofile' : |d.f r' - f₀ - d₁ * r'| ≤ error) :
    (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹))⁻¹ *
        μ univ ≤
      ENNReal.ofReal (64 * (max p.κ (d.K k)) ^ 2 * p.κ *
        d.N k ^ (-d₁ * (r' - p.r (p.lev a)) + 2 * error + τ + ε)) *
          ENNReal.ofReal ((2 * mesh) ^ 3) := by
  have hN : 1 ≤ d.N k := by linarith [hd.1 k]
  have hκ : 0 ≤ p.κ := by linarith [hp.1]
  have hraw := source_physical_cell_mass_cap hd hp a r' hr' hr'L hscale hmesh hwidth
    μ hμ _ c hF hcell (hpure _ μ hμ hbase r' hr' hr'L)
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (pure_cap_coefficient hN hκ (profile_increment_for_cap hprofile hprofile')) zero_le)

end Prepared

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
