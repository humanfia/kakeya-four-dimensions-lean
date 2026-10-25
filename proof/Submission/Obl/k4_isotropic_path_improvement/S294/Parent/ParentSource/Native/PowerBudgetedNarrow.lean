-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PowerBudgetedNarrow, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PowerBudgetedNarrow.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PowerBudgetedNarrow.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PowerBudgetedNarrow.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativePowerNet
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeUniformRadii
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.SaturationNarrow
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.WindowGridNumerics

/-! The actual power-budgeted saturated capture gives the frozen weak
narrow atlas. Its output format is fixed before the requested list slack. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped ENNReal BigOperators RealInnerProductSpace

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {z mesh aEntropy fraction : ℝ}
  {F : PaletteFamily Q i stop mesh
    (d.N k ^ aEntropy / palettePruningThreshold ⌈(4 * p.κ + 6) ^ 2⌉₊) (lightParentThreshold p.κ)}
  (P : PaletteStripSaturation F (d.N k ^ (-z)) fraction)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem PaletteStripSaturation.narrow_of_native_power_bounds (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hm : 0 < m) (hB : ∀ w, 0 ≤ d.B k w)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {x | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ x ∈ p.F b})
    (hi : i < m) (hstop : stop < m) (himiddle : 1 / 4 ≤ s i ∧ s i ≤ 1 / 2)
    {gain u0 β α E : ℝ} (t : T) (J Jpred : ℕ)
    (hz : 0 < z) (haEntropy : 0 ≤ aEntropy) (hmesh : mesh ≤ d.N k ^ (-z))
    (hfraction : 0 < fraction)
    (htu : u t = z / 16) (hτ : τ ≤ d.S * z / 4096)
    (hβlow : u0 ≤ β) (hβhigh : β ≤ 4 * gain)
    (hJ : Mp ≤ J) (htime : (2 : ℝ) ^ p.T i ≤ d.N k ^ J)
    (hE : 100 ≤ E) (hκE : 3 * p.κ ≤ E) (hmκE : (m : ℝ) * p.κ ≤ E)
    (hfloorConstant : 12928 / fraction ≤ E) (hcapConstant : 819200 * (m : ℝ) ≤ E)
    (hpredCount : fraction⁻¹ ≤ (Jpred : ℝ)) (hpredEnvelope : 250 * (Jpred : ℝ) ≤ E)
    (hEpower : E ≤ d.N k ^ (z / 32))
    (hpower : StripSecondScaleBounds (d.N k) E 3 z aEntropy (d.S * z / 64) α (z / 32) 3 4)
    (hgain : δ₀ * d.L + z / 32 + β * d.L ≤ z / 4)
    (hmass : ENNReal.ofReal (9 * p.κ⁻¹ / 64) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (P.captureResidual w)) :
    narrow (d.N k) d.L (d.W k) (d.ω k) (d.ν k) (d.E k) (d.B k) m s p.r p.T p.nw gain u0 p.κ
      (stripMergedOutputExponent Mp J ⌈z / 4⌉₊ (2 * 3 + ⌈2 * aEntropy⌉₊ + 2) (4 * Mp + 3))
      (max Dp 1) α p.C p.lev p.γ p.j p.A p.F H := by
  classical
  have hN : 1 ≤ d.N k := by linarith [hpower.N_two]
  have hNpos : 0 < d.N k := zero_lt_one.trans_le hN
  have hκE' : p.κ ≤ E := by linarith [hp.1]
  have hK := native_palette_integer_bounds hp.1
  have hS : 0 < d.S := hd.2.2.2.2.2.2.1
  have hcapExponent : -d.S * u t + 2 * τ ≤ -(d.S * z / 64) := by
    rw [htu]
    exact native_angular_exponent_budget hS hz hτ
  obtain ⟨hr₁, hr₂, hmeshes, hr₂1, hsmall, _, _, _, _⟩ := hpower.scales
  obtain ⟨hsmallOverlap, hpackingRadius, hoverlapRadius, hcapScale⟩ :=
    hpower.native_angular_radii hz.le hp.1 hκE' hEpower
  have hcapScale' : p.κ * (d.N k ^ (-z / 16) / E) ≤ δ (d.N k) (u t) := by
    simpa only [htu] using hcapScale
  have hraw : d.N k ^ (-z) + 2 * mesh ≤ 3 * d.N k ^ (-z) := by linarith
  obtain ⟨g, hradius, hcount, hcountPower, _, hbins, hbinUpper, hnormal,
      hn, he, hen, hoffset, hnet, hsmall', hwidth, hcap, hcost⟩ :=
    P.exists_native_power_net hd hp hm hHE hK.1 hK.2 hfraction haEntropy t
      hpower.N_two hκE hpower.E_le_N hfloorConstant hcapConstant hcapExponent hcapScale'
      hpower.packing hpower.overlap (by positivity) hraw hr₁ hr₂ hmeshes hr₂1 hsmall
      hsmallOverlap hpackingRadius hoverlapRadius
  have hcap' (b : Fin p.C) (hb : F.active b) (x : StripSpace) :
      Q.velocityPosterior b (Metric.closedBall x
        (32 * (1 + 2 * p.κ) * (3 * d.N k ^ (-z) + (1 + 2 * p.κ) * d.N k ^ (-z / 2)) / g.radius)) ≤
          ENNReal.ofReal (E ^ 4 * d.N k ^ (-(d.S * z / 64))) := by
    have hR := hoverlapRadius
    rw [← hradius] at hR
    exact (measure_mono (fun _ hx => hx.trans hR)).trans (hcap b hb x)
  have hradiusBound : g.radius ≤ d.N k ^ (-(z / 4)) := by
    rw [hradius, show -z / 4 = -(z / 4) by ring]
  exact P.narrow_of_large_capture hd hp hpower.N_two hB hHE hH hi hstop himiddle
    hβlow hβhigh g J ⌈z / 4⌉₊ (2 * 3 + ⌈2 * aEntropy⌉₊ + 2) Jpred
    hJ htime hE hpower.E_le_N hκE' hmκE hpredCount hpredEnvelope
    (by rw [hradius]; exact hr₂) (by rw [hradius]; exact hr₂1)
    (by rw [hradius]; exact hpower.inverseRadius)
    he hn hen hbins hbinUpper hoffset hcountPower hnormal hwidth
    (by rw [hradius]; exact hmeshes) (by nlinarith [Real.rpow_nonneg hNpos.le (-z)]) hnet hsmall'
    hcap' hcost hpower.slack hpower.determinantSlack hradiusBound hgain hmass

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
