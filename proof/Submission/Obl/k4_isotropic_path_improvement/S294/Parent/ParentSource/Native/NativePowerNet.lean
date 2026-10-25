-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativePowerNet, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativePowerNet.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativePowerNet.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativePowerNet.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PaletteStripSaturation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeAngularCap
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeScaleNumerics
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripPowerBudgetedNet

/-! An actual saturated native family has a power-budgeted two-scale net.
The heavy floor comes from its original palette certificate, and the ball
cap comes from the same original native velocity posterior. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped RealInnerProductSpace

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop Kpalette : ℕ}
  {a aEntropy r fraction : ℝ}
  {F : PaletteFamily Q i stop a
    (d.N k ^ aEntropy / palettePruningThreshold Kpalette) (lightParentThreshold p.κ)}
  (P : PaletteStripSaturation F r fraction)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem PaletteStripSaturation.exists_native_power_net (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hm : 0 < m) (hHE : ∀ w, H w ⊆ d.E k w)
    (hK : 1 ≤ Kpalette) (hKupper : (Kpalette : ℝ) ≤ 101 * p.κ ^ 2)
    (hfraction : 0 < fraction) (haEntropy : 0 ≤ aEntropy)
    {E v r₀ r₁ r₂ Rcap : ℝ} (t : T)
    (hN : 2 ≤ d.N k) (hE : 3 * p.κ ≤ E) (hEN : E ≤ d.N k)
    (hfloorConstant : 12928 / fraction ≤ E) (hcapConstant : 819200 * (m : ℝ) ≤ E)
    (hcapExponent : -d.S * u t + 2 * τ ≤ -v)
    (hcapScale : p.κ * Rcap ≤ δ (d.N k) (u t))
    (hpacking : 2 * E ^ (4 + 2 * 3) * d.N k ^ (2 * aEntropy - v) ≤ 1)
    (hoverlap : 900 * E ^ (4 * 3 + 4 + 8) * d.N k ^ (4 * aEntropy - v) ≤ 1)
    (hr₀ : 0 ≤ r₀) (hraw : r + 2 * a ≤ r₀)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hmeshes : r₁ ≤ r₂) (hr₂1 : r₂ ≤ 1)
    (hsmall : 4 * r₀ ≤ r₁) (hsmallOverlap : 4 * (r₀ + (1 + 2 * p.κ) * r₁) ≤ r₂)
    (hpackingRadius : 32 * (1 + 2 * p.κ) * r₀ / r₁ ≤ Rcap)
    (hoverlapRadius : 32 * (1 + 2 * p.κ) * (r₀ + (1 + 2 * p.κ) * r₁) / r₂ ≤ Rcap) :
    ∃ g : StripRefinement (Fin p.C),
      g.radius = r₂ ∧ 0 < g.count ∧
      (g.count : ℝ) ≤ d.N k ^ (2 * 3 + ⌈2 * aEntropy⌉₊ + 2) ∧
      (g.count : ℝ) ≤ 3 * (E ^ 3 * d.N k ^ aEntropy) ^ 2 ∧
      p.κ ≤ (g.bins : ℝ) * g.radius ∧ (g.bins : ℝ) * g.radius ≤ 2 * E ∧
      (g.normalBudget : ℝ) ≤ 5 * E ∧
      (∀ b j, ‖g.normal b j‖ = 1) ∧ (∀ b j, ‖g.tangent b j‖ = 1) ∧
      (∀ b j, inner ℝ (g.tangent b j) (g.normal b j) = 0) ∧
      (∀ b j, |g.offset b j| ≤ 3 * E) ∧
      (∀ b, F.active b → ∀ e, ∀ q ∈ P.predictions b e, ∃ j,
        stripParametersClose q.val.1 q.val.2 (g.normal b j) (g.offset b j) r₁) ∧
      4 * (r₀ + (1 + 2 * p.κ) * r₁) ≤ g.radius ∧
      r₀ + (1 + 2 * p.κ) * r₁ + 3 * (1 + 2 * p.κ) * g.radius ≤
        (g.normalBudget : ℝ) * g.radius ∧
      (∀ b, F.active b → ∀ x : StripSpace,
        Q.velocityPosterior b (Metric.closedBall x Rcap) ≤ ENNReal.ofReal (E ^ 4 * d.N k ^ (-v))) ∧
      (g.count : ENNReal) ^ 2 * ENNReal.ofReal (E ^ 4 * d.N k ^ (-v)) ≤
        ENNReal.ofReal (p.κ⁻¹ / 64) := by
  classical
  have hNpos : 0 < d.N k := by linarith
  have hκpos : 0 < p.κ := zero_lt_one.trans_le hp.1
  have hκE : p.κ ≤ E := by linarith [hp.1]
  have hEone : 1 ≤ E := hp.1.trans hκE
  have hε : 0 ≤ E ^ 4 * d.N k ^ (-v) := by positivity
  have hA : 0 < d.N k ^ aEntropy / palettePruningThreshold Kpalette :=
    div_pos (Real.rpow_pos_of_pos hNpos _) (palettePruningThreshold_pos hK)
  have hInv := native_palette_inverse_floor hκpos.le hκE hK hKupper hfraction hfloorConstant
    (Real.rpow_nonneg hNpos.le aEntropy)
  have hcap (b : Fin p.C) (hb : F.active b) (x : StripSpace) :
      Q.velocityPosterior b (Metric.closedBall x Rcap) ≤ ENNReal.ofReal (E ^ 4 * d.N k ^ (-v)) := by
    have h := F.native_velocity_ball_cap hd hp hm hHE b hb t hcapScale x
    apply h.trans
    apply ENNReal.ofReal_le_ofReal
    exact native_angular_coefficient_envelope m hκpos.le hκE hcapConstant
      (Real.rpow_nonneg hNpos.le _) (Real.rpow_le_rpow_of_exponent_le (by linarith) hcapExponent)
  let ι := fun b => {z : ℕ × UnitStripParameter // F.active b ∧ z.2 ∈ P.predictions b z.1}
  let n := fun b (z : ι b) => z.val.2.val.1
  let β := fun b (z : ι b) => z.val.2.val.2
  have hprob (b : Fin p.C) (hb : Nonempty (ι b)) : IsProbabilityMeasure (Q.velocityPosterior b) := by
    obtain ⟨z⟩ := hb
    exact Q.velocity_posterior_probability hd b (F.current_positive b z.property.1)
  have hn (b : Fin p.C) (z : ι b) : ‖n b z‖ = 1 := z.val.2.property
  have hmass (b : Fin p.C) (z : ι b) :
      fraction / (d.N k ^ aEntropy / palettePruningThreshold Kpalette) ≤
        (Q.velocityPosterior b).real (boundedStrip (n b z) (β b z) r₀ (2 * p.κ)) := by
    letI : IsProbabilityMeasure (Q.velocityPosterior b) := hprob b ⟨z⟩
    exact (P.heavy b z.property.1 z.val.1 z.val.2 z.property.2).trans
      (measureReal_mono (fun x hx => ⟨hx.1, hx.2.trans hraw⟩))
  have hcap' (b : Fin p.C) (hb : Nonempty (ι b)) : ∀ x : StripSpace,
      Q.velocityPosterior b (Metric.closedBall x Rcap) ≤ ENNReal.ofReal (E ^ 4 * d.N k ^ (-v)) := by
    obtain ⟨z⟩ := hb
    exact hcap b z.property.1
  obtain ⟨g, hradius, hcount, hcountPower, hcountEnvelope, hbins, hbinUpper, hnormal,
      hn', ht', horth, hoffset, hnet, hsmall', hwidth, _⟩ :=
    exists_power_budgeted_second_scale_refinement Q.velocityPosterior hprob n β 3 4
      hN hp.1 hE hEN (div_pos hfraction hA) hε haEntropy hInv le_rfl hpacking hoverlap
      hr₀ hr₁ hr₂ hmeshes hr₂1 hsmall hsmallOverlap hpackingRadius hoverlapRadius hn hmass hcap'
  have hpair := strip_pair_overlap_of_power_budget hNpos hEone
    (show 0 ≤ (g.count : ℝ) by positivity) hε 3 4 hcountEnvelope le_rfl hoverlap
  have hpair' := hpair.trans (native_overlap_original_budget hp.1 hκE)
  have hpairENN := ENNReal.ofReal_le_ofReal hpair'
  have hcost : (g.count : ENNReal) ^ 2 * ENNReal.ofReal (E ^ 4 * d.N k ^ (-v)) ≤
      ENNReal.ofReal (p.κ⁻¹ / 64) := by
    simpa only [ENNReal.ofReal_mul (sq_nonneg (g.count : ℝ)),
      ENNReal.ofReal_pow (Nat.cast_nonneg g.count), ENNReal.ofReal_natCast] using hpairENN
  refine ⟨g, hradius, hcount, hcountPower, hcountEnvelope, hbins, hbinUpper, hnormal,
    hn', ht', horth, hoffset, ?_, hsmall', hwidth, hcap, hcost⟩
  intro b hb e q hq
  exact hnet b ⟨(e, q), hb, hq⟩

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
