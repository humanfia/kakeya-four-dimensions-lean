-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripSecondScaleNet, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripSecondScaleNet.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripSecondScaleNet.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripSecondScaleNet.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripSecondScaleNet.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripNet
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripMergedCells

/-! The first mesh builds a finite heavy net. The second mesh determines
output frames and merge labels; its geometric budgets depend only on the
actual path slack, independently of the heavy-strip floor. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips
open scoped RealInnerProductSpace

theorem exists_second_scale_strip_refinement_of_active {P : Type} {ι : P → Type}
    (μ : P → Measure StripSpace)
    (hprob : ∀ b, Nonempty (ι b) → IsProbabilityMeasure (μ b))
    (n : (b : P) → ι b → StripSpace) (β : (b : P) → ι b → ℝ)
    {K floor ε r₀ r₁ r₂ : ℝ} (hn : ∀ b i, ‖n b i‖ = 1)
    (hK : 1 ≤ K) (hfloor : 0 < floor) (hε : 0 ≤ ε) (hr₀ : 0 ≤ r₀)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hmeshes : r₁ ≤ r₂) (hr₂1 : r₂ ≤ 1)
    (hsmall : 4 * r₀ ≤ r₁)
    (hmass : ∀ b i, floor ≤ (μ b).real (boundedStrip (n b i) (β b i) r₀ (2 * K)))
    (hcap : ∀ b, Nonempty (ι b) → ∀ x,
      (μ b) (Metric.closedBall x (32 * (1 + 2 * K) * r₀ / r₁)) ≤ ENNReal.ofReal ε)
    (heps : 2 * ε ≤ floor ^ 2) :
    ∃ d : StripRefinement P,
      d.radius = r₂ ∧ 0 < d.count ∧ (d.count : ℝ) ≤ 2 / floor ^ 2 + 1 ∧
      K ≤ (d.bins : ℝ) * d.radius ∧ (d.bins : ℝ) * d.radius ≤ 2 * K ∧
      (d.normalBudget : ℝ) ≤ 14 * K ∧
      (∀ b i, ‖d.normal b i‖ = 1) ∧ (∀ b i, ‖d.tangent b i‖ = 1) ∧
      (∀ b i, inner ℝ (d.tangent b i) (d.normal b i) = 0) ∧
      (∀ b i, |d.offset b i| ≤ 3 * K) ∧
      (∀ b i, ∃ j,
        stripParametersClose (n b i) (β b i) (d.normal b j) (d.offset b j) r₁) ∧
      r₀ + (1 + 2 * K) * r₁ + 3 * (1 + 2 * K) * d.radius ≤
        (d.normalBudget : ℝ) * d.radius := by
  obtain ⟨C, n', β', hC, hcard, hn', hβ', hnet⟩ :=
    exists_uniform_heavy_strip_parameter_net_of_active μ hprob n β hn hfloor hε hr₀
      (by linarith) hr₁ hsmall hmass hcap heps
  let d : StripRefinement P :=
    { count := C
      bins := stripMidpointBinCount K r₂
      normalBudget := ⌈5 + 8 * K⌉₊
      radius := r₂
      normal := n'
      tangent := fun b i => stripTangent (n' b i)
      offset := β' }
  refine ⟨d, rfl, hC, hcard, stripMidpointBinCount_lower hr₂, ?_, ?_, hn', ?_, ?_, ?_, hnet, ?_⟩
  · exact (stripMidpointBinCount_upper (by linarith) hr₂).trans (by linarith)
  · have hceil := Nat.ceil_lt_add_one (show 0 ≤ 5 + 8 * K by linarith)
    change (⌈5 + 8 * K⌉₊ : ℝ) ≤ 14 * K
    linarith
  · intro b i
    exact (stripTangent_norm _).trans (hn' b i)
  · intro b i
    exact stripTangent_inner _
  · intro b i
    exact (hβ' b i).trans (by linarith)
  · have hr₀₂ : r₀ ≤ r₂ := by linarith
    have hw : r₀ + (1 + 2 * K) * r₁ + 3 * (1 + 2 * K) * r₂ ≤ (5 + 8 * K) * r₂ := by
      calc
        _ ≤ r₂ + (1 + 2 * K) * r₂ + 3 * (1 + 2 * K) * r₂ := by gcongr
        _ = _ := by ring
    exact hw.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil (5 + 8 * K)) hr₂.le)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
