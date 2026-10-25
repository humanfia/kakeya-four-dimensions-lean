-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripPowerBudgetedNet, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripPowerBudgetedNet.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripPowerBudgetedNet.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripPowerBudgetedNet.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripPowerBudgetedNet.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripSecondScaleNet
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripPackingPowerBudgets

/-! A coarse-heavy floor with a fixed entropy power produces a concrete
second-scale net. All frame bounds use the actual path envelope, and its
global far-overlap cost is already below the original residual budget. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips
open scoped RealInnerProductSpace

theorem exists_power_budgeted_second_scale_refinement {P : Type} {ι : P → Type}
    (μ : P → Measure StripSpace)
    (hprob : ∀ b, Nonempty (ι b) → IsProbabilityMeasure (μ b))
    (n : (b : P) → ι b → StripSpace) (β : (b : P) → ι b → ℝ)
    {N K E floor ε a v r₀ r₁ r₂ Rcap : ℝ} (p q : ℕ)
    (hN : 2 ≤ N) (hK : 1 ≤ K) (hE : 3 * K ≤ E)
    (hEN : E ≤ N) (hfloor : 0 < floor) (hε : 0 ≤ ε) (ha : 0 ≤ a)
    (hInv : floor⁻¹ ≤ E ^ p * N ^ a) (hεpow : ε ≤ E ^ q * N ^ (-v))
    (hpack : 2 * E ^ (q + 2 * p) * N ^ (2 * a - v) ≤ 1)
    (hoverlap : 900 * E ^ (4 * p + q + 8) * N ^ (4 * a - v) ≤ 1)
    (hr₀ : 0 ≤ r₀) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hmeshes : r₁ ≤ r₂)
    (hr₂1 : r₂ ≤ 1) (hsmall : 4 * r₀ ≤ r₁)
    (hsmallOverlap : 4 * (r₀ + (1 + 2 * K) * r₁) ≤ r₂)
    (hpackingRadius : 32 * (1 + 2 * K) * r₀ / r₁ ≤ Rcap)
    (hoverlapRadius : 32 * (1 + 2 * K) * (r₀ + (1 + 2 * K) * r₁) / r₂ ≤ Rcap)
    (hn : ∀ b j, ‖n b j‖ = 1)
    (hmass : ∀ b j, floor ≤ (μ b).real (boundedStrip (n b j) (β b j) r₀ (2 * K)))
    (hcap : ∀ b, Nonempty (ι b) → ∀ x : StripSpace,
      μ b (Metric.closedBall x Rcap) ≤ ENNReal.ofReal ε) :
    ∃ d : StripRefinement P,
      d.radius = r₂ ∧ 0 < d.count ∧
      (d.count : ℝ) ≤ N ^ (2 * p + ⌈2 * a⌉₊ + 2) ∧
      (d.count : ℝ) ≤ 3 * (E ^ p * N ^ a) ^ 2 ∧
      K ≤ (d.bins : ℝ) * d.radius ∧ (d.bins : ℝ) * d.radius ≤ 2 * E ∧
      (d.normalBudget : ℝ) ≤ 5 * E ∧
      (∀ b j, ‖d.normal b j‖ = 1) ∧ (∀ b j, ‖d.tangent b j‖ = 1) ∧
      (∀ b j, inner ℝ (d.tangent b j) (d.normal b j) = 0) ∧
      (∀ b j, |d.offset b j| ≤ 3 * E) ∧
      (∀ b j, ∃ t, stripParametersClose (n b j) (β b j) (d.normal b t) (d.offset b t) r₁) ∧
      4 * (r₀ + (1 + 2 * K) * r₁) ≤ d.radius ∧
      r₀ + (1 + 2 * K) * r₁ + 3 * (1 + 2 * K) * d.radius ≤
        (d.normalBudget : ℝ) * d.radius ∧
      ∀ b, Nonempty (ι b) → μ b
        (stripFarOverlap (d.normal b) (d.offset b) (r₀ + (1 + 2 * K) * r₁) d.radius (2 * K)) ≤
          ENNReal.ofReal ((100 * E ^ 8)⁻¹) := by
  have hN1 : 1 ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have hE1 : 1 ≤ E := by linarith
  have hKE : K ≤ E := by linarith
  have hpackε := strip_packing_error_of_power_budget hNpos hE1 hfloor hε p q hInv hεpow hpack
  have hcap₁ (b : P) (hb : Nonempty (ι b)) (x : StripSpace) :
      μ b (Metric.closedBall x (32 * (1 + 2 * K) * r₀ / r₁)) ≤ ENNReal.ofReal ε :=
    (measure_mono (fun _ hy => hy.trans hpackingRadius)).trans (hcap b hb x)
  obtain ⟨d, hrad, hcountpos, hcount, hbins, hbinsUpper, hnormal, hn', he', hen, hβ, hnet, hwidth⟩ :=
    exists_second_scale_strip_refinement_of_active μ hprob n β hn hK hfloor hε hr₀ hr₁ hr₂
      hmeshes hr₂1 hsmall hmass hcap₁ hpackε
  have hcountEnvelope := strip_heavy_net_count_envelope hN1 hE1 hfloor p ha hInv hcount
  have hcountpow := strip_heavy_net_count_power hN hE1 hEN hfloor p ⌈2 * a⌉₊ ha
    (Nat.le_ceil _) hInv hcount
  have herror := strip_pair_overlap_of_power_budget hNpos hE1
    (show 0 ≤ (d.count : ℝ) by positivity) hε p q hcountEnvelope hεpow hoverlap
  have herrorENN : (d.count : ENNReal) ^ 2 * ENNReal.ofReal ε ≤
      ENNReal.ofReal ((100 * E ^ 8)⁻¹) := by
    have h := ENNReal.ofReal_le_ofReal herror
    simpa only [ENNReal.ofReal_mul (sq_nonneg (d.count : ℝ)),
      ENNReal.ofReal_pow (Nat.cast_nonneg d.count), ENNReal.ofReal_natCast] using h
  refine ⟨d, hrad, hcountpos, hcountpow, hcountEnvelope, hbins, hbinsUpper.trans (by linarith),
    hnormal.trans (by linarith), hn', he', hen, ?_, hnet, ?_, hwidth, ?_⟩
  · intro b j
    exact (hβ b j).trans (by linarith)
  · rwa [hrad]
  · intro b hb
    have hcap₂ (x : StripSpace) : μ b (Metric.closedBall x
        (32 * (1 + 2 * K) * (r₀ + (1 + 2 * K) * r₁) / d.radius)) ≤ ENNReal.ofReal ε := by
      have hR : 32 * (1 + 2 * K) * (r₀ + (1 + 2 * K) * r₁) / d.radius ≤ Rcap := by
        rwa [hrad]
      exact (measure_mono (fun _ hy => hy.trans hR)).trans (hcap b hb x)
    have hfar := stripFarOverlap_mass_le (μ b) (d.normal b) (d.offset b) (hn' b)
      (by linarith) (hrad ▸ hr₂) (by rwa [hrad]) hcap₂
    exact hfar.trans (by simpa only [Fintype.card_fin] using herrorENN)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
