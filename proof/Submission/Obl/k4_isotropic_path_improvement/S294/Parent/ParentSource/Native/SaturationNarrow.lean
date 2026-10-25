-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.SaturationNarrow, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/SaturationNarrow.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/SaturationNarrow.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/SaturationNarrow.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.SaturationOverlap
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.SaturationPredictions
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FinitePredictedNarrow

/-! The COMPLETE saturated capture gives the frozen weak narrow alternative.
One native overlap cost is charged to ORIGINAL mass; per-fine-state lists
have fixed size, independently of the coarse heavy-net size. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped ENNReal BigOperators RealInnerProductSpace

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
  {F : PaletteFamily Q i stop a A θ} (P : PaletteStripSaturation F r fraction)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem PaletteStripSaturation.narrow_of_large_capture (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hN : 2 ≤ d.N k) (hB : ∀ w, 0 ≤ d.B k w)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (hi : i < m) (hstop : stop < m) (himiddle : 1 / 4 ≤ s i ∧ s i ≤ 1 / 2)
    {gain u0 β α loss stripExponent E width r₁ ε : ℝ}
    (hβlow : u0 ≤ β) (hβhigh : β ≤ 4 * gain)
    (g : StripRefinement (Fin p.C)) (J Uexp V Jpred : ℕ)
    (hJ : Mp ≤ J) (htime : (2 : ℝ) ^ p.T i ≤ d.N k ^ J)
    (hE : 100 ≤ E) (hEN : E ≤ d.N k) (hκE : p.κ ≤ E) (hmκE : (m : ℝ) * p.κ ≤ E)
    (hpredCount : fraction⁻¹ ≤ (Jpred : ℝ)) (hpredEnvelope : 250 * (Jpred : ℝ) ≤ E)
    (hr : 0 < g.radius) (hr1 : g.radius ≤ 1) (hrinv : g.radius⁻¹ ≤ d.N k ^ Uexp)
    (he : ∀ b j, ‖g.tangent b j‖ = 1) (hn : ∀ b j, ‖g.normal b j‖ = 1)
    (hen : ∀ b j, inner ℝ (g.tangent b j) (g.normal b j) = 0)
    (hbins : p.κ ≤ (g.bins : ℝ) * g.radius)
    (hbinUpper : (g.bins : ℝ) * g.radius ≤ 2 * E)
    (hoffset : ∀ b j, |g.offset b j| ≤ 3 * E)
    (hcount : (g.count : ℝ) ≤ d.N k ^ V) (hnormal : (g.normalBudget : ℝ) ≤ 5 * E)
    (hwidth : width + 3 * (1 + 2 * p.κ) * g.radius ≤ (g.normalBudget : ℝ) * g.radius)
    (hmeshes : r₁ ≤ g.radius) (hrawWidth : r + (1 + 2 * p.κ) * r₁ ≤ width)
    (hnet : ∀ b, F.active b → ∀ e, ∀ q ∈ P.predictions b e, ∃ j,
      stripParametersClose q.val.1 q.val.2 (g.normal b j) (g.offset b j) r₁)
    (hsmall : 4 * width ≤ g.radius)
    (hcap : ∀ b, F.active b → ∀ x : StripSpace,
      Q.velocityPosterior b (Metric.closedBall x (32 * (1 + 2 * p.κ) * width / g.radius)) ≤ ENNReal.ofReal ε)
    (hcost : (g.count : ENNReal) ^ 2 * ENNReal.ofReal ε ≤ ENNReal.ofReal (p.κ⁻¹ / 64))
    (hslack : 100 * E ^ 8 ≤ d.N k ^ α) (hdetSlack : 6 * E ^ 2 ≤ d.N k ^ loss)
    (hradius : g.radius ≤ d.N k ^ (-stripExponent))
    (hgain : δ₀ * d.L + loss + β * d.L ≤ stripExponent)
    (hmass : ENNReal.ofReal (9 * p.κ⁻¹ / 64) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (P.captureResidual w)) :
    narrow (d.N k) d.L (d.W k) (d.ω k) (d.ν k) (d.E k) (d.B k) m s p.r p.T p.nw gain u0 p.κ
      (stripMergedOutputExponent Mp J Uexp V (4 * Mp + 3)) (max Dp 1) α
      p.C p.lev p.γ p.j p.A p.F H := by
  classical
  obtain ⟨params, hparams⟩ := P.exists_prediction_arrays Jpred hpredCount
  obtain ⟨R, hR, hRH, hRmass, hRcover⟩ := P.capture_after_overlaps hd hp hHE hH hi hstop
    g.count g.normal g.offset hr hsmall (fun b _ j => hn b j) hcap hcost hmass
  let net : StripRefinement (p.StripLevel i) :=
    { count := g.count, bins := g.bins, normalBudget := g.normalBudget, radius := g.radius,
      normal := fun b => g.normal b.val, tangent := fun b => g.tangent b.val,
      offset := fun b => g.offset b.val }
  let rawNormal := fun (t : Fin Jpred) (b : p.StripLevel i) (f : Fin p.C) =>
    (params b.val (F.coding.code f) t).val.1
  let rawOffset := fun (t : Fin Jpred) (b : p.StripLevel i) (f : Fin p.C) =>
    (params b.val (F.coding.code f) t).val.2
  have hvel (b : p.StripLevel i) (x : (ℕ × (Fin 6 → ℝ)) × ℝ) :
      packetVelocity (((2 : ℝ) ^ p.T i)⁻¹) (p.stripParent i b).frame
        (p.stripParent i b).velocity x.1 = p.normalizedVelocity b.val x := by
    simp only [packetVelocity, PathData.stripParent, PathData.normalizedVelocity, b.property, v,
      Submission.Lib.K4XInterface.gv]
  have hcover : ∀ w, R w ⊆ {x | ∃ (b : p.StripLevel i) (f : Fin p.C) (t : Fin Jpred),
      p.γ b = w ∧ x ∈ (p.stripParent i b).incidences ∧
      x ∈ p.packetWitness m stop (p.γ b) f ∧
      packetVelocity (((2 : ℝ) ^ p.T i)⁻¹) (p.stripParent i b).frame
        (p.stripParent i b).velocity x.1 ∈ affineStrip (rawNormal t b f) (rawOffset t b f) r ∧
      (∃ j, stripParametersClose (rawNormal t b f) (rawOffset t b f)
        (net.normal b j) (net.offset b j) r₁) ∧
      packetVelocity (((2 : ℝ) ^ p.T i)⁻¹) (p.stripParent i b).frame
        (p.stripParent i b).velocity x.1 ∉
          stripFarOverlap (net.normal b) (net.offset b) width net.radius (2 * p.κ)} := by
    intro w x hx
    obtain ⟨b, hbi, hbγ, hb, hxb, f, hf, hfγ, hxf, ⟨q, hq, hxstrip⟩, hxgood⟩ := hRcover w x hx
    obtain ⟨t, ht⟩ := hparams b hb (F.coding.code f) q hq
    let b' : p.StripLevel i := ⟨b, hbi⟩
    have hnEq : rawNormal t b' f = q.val.1 := congrArg (fun z : UnitStripParameter => z.val.1) ht
    have hβEq : rawOffset t b' f = q.val.2 := congrArg (fun z : UnitStripParameter => z.val.2) ht
    refine ⟨b', f, t, hbγ, hxb, ?_, ?_, ?_, ?_⟩
    · simpa only [b', hbγ] using hxf
    · simpa only [hvel, hnEq, hβEq] using hxstrip
    · simpa only [net, hnEq, hβEq] using hnet b hb (F.coding.code f) q hq
    · simpa only [hvel, net] using hxgood
  exact hp.narrow_of_finitely_predicted_strip_cover hN hB i stop hi himiddle hβlow hβhigh
    net J Uexp V Jpred hJ htime hE hEN hκE hmκE hpredEnvelope hr hr1 hrinv
    (fun b j => he b.val j) (fun b j => hn b.val j) (fun b j => hen b.val j)
    hbins hbinUpper (fun b j => hoffset b.val j) hcount hnormal hwidth hmeshes hrawWidth
    rawNormal rawOffset R H hRH hcover hslack hdetSlack hradius hgain hRmass

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
