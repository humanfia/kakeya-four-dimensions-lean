-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripNet, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripNet.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripNet.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripNet.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripNet.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripCover
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripAtlas
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripGeometryBudget

/-! Package the fixed-palette strip packing as the concrete refinement data
used by the original-law width-system assembly. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips
open scoped RealInnerProductSpace

theorem exists_packed_strip_refinement_of_active {P : Type} {ι : P → Type}
    (μ : P → Measure StripSpace)
    (hprob : ∀ b, Nonempty (ι b) → IsProbabilityMeasure (μ b))
    (n : (b : P) → ι b → StripSpace) (β : (b : P) → ι b → ℝ)
    {K κ ε r ρ T : ℝ} (hn : ∀ b i, ‖n b i‖ = 1)
    (hK : 0 ≤ K) (hκ : 0 < κ) (hε : 0 ≤ ε) (hr : 0 ≤ r) (hT : 0 ≤ T)
    (hρ : 0 < ρ) (hsmall : 4 * r ≤ ρ)
    (hmass : ∀ b i, κ ≤ (μ b).real (boundedStrip (n b i) (β b i) r T))
    (hcap : ∀ b, Nonempty (ι b) → ∀ x,
      (μ b) (Metric.closedBall x (32 * (1 + T) * r / ρ)) ≤ ENNReal.ofReal ε)
    (heps : 2 * ε ≤ κ ^ 2) :
    ∃ d : StripRefinement P,
      d.radius = ρ ∧ d.bins = stripMidpointBinCount K ρ ∧ d.normalBudget = ⌈2 + T⌉₊ ∧
      0 < d.count ∧ (d.count : ℝ) ≤ 2 / κ ^ 2 + 1 ∧
      K ≤ (d.bins : ℝ) * d.radius ∧ (d.bins : ℝ) * d.radius ≤ K + ρ ∧
      (∀ b i, ‖d.normal b i‖ = 1) ∧ (∀ b i, ‖d.tangent b i‖ = 1) ∧
      (∀ b i, inner ℝ (d.tangent b i) (d.normal b i) = 0) ∧
      (∀ b i, |d.offset b i| ≤ T + r) ∧
      ∀ b i x, ‖x‖ ≤ T → x ∈ affineStrip (n b i) (β b i) r →
        x ∈ ⋃ j, affineStrip (d.normal b j) (d.offset b j) ((d.normalBudget : ℝ) * d.radius) := by
  obtain ⟨C, n', β', hC, hcard, hn', hβ', hcover⟩ := exists_uniform_heavy_strip_cover_of_active μ hprob n β
    hn hκ hε hr hT hρ hsmall hmass hcap heps
  let d : StripRefinement P :=
    { count := C
      bins := stripMidpointBinCount K ρ
      normalBudget := ⌈2 + T⌉₊
      radius := ρ
      normal := n'
      tangent := fun b i => stripTangent (n' b i)
      offset := β' }
  refine ⟨d, rfl, rfl, rfl, hC, hcard, stripMidpointBinCount_lower hρ,
    stripMidpointBinCount_upper hK hρ, hn', ?_, ?_, hβ', ?_⟩
  · intro b i
    exact (stripTangent_norm _).trans (hn' b i)
  · intro b i
    exact stripTangent_inner _
  · intro b i x hx hxi
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover b i x hx hxi)
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    have hwidth : r + (1 + T) * ρ ≤ (⌈2 + T⌉₊ : ℝ) * ρ := by
      calc
        _ ≤ ρ + (1 + T) * ρ := by linarith
        _ = (2 + T) * ρ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil (2 + T)) hρ.le
    exact hj.trans hwidth

theorem exists_packed_strip_refinement {P : Type} {ι : P → Type}
    (μ : P → Measure StripSpace)
    [∀ b, IsProbabilityMeasure (μ b)]
    (n : (b : P) → ι b → StripSpace) (β : (b : P) → ι b → ℝ)
    {K κ ε r ρ T : ℝ} (hn : ∀ b i, ‖n b i‖ = 1)
    (hK : 0 ≤ K) (hκ : 0 < κ) (hε : 0 ≤ ε) (hr : 0 ≤ r) (hT : 0 ≤ T)
    (hρ : 0 < ρ) (hsmall : 4 * r ≤ ρ)
    (hmass : ∀ b i, κ ≤ (μ b).real (boundedStrip (n b i) (β b i) r T))
    (hcap : ∀ b x, (μ b) (Metric.closedBall x (32 * (1 + T) * r / ρ)) ≤ ENNReal.ofReal ε)
    (heps : 2 * ε ≤ κ ^ 2) :
    ∃ d : StripRefinement P,
      d.radius = ρ ∧ d.bins = stripMidpointBinCount K ρ ∧ d.normalBudget = ⌈2 + T⌉₊ ∧
      0 < d.count ∧ (d.count : ℝ) ≤ 2 / κ ^ 2 + 1 ∧
      K ≤ (d.bins : ℝ) * d.radius ∧ (d.bins : ℝ) * d.radius ≤ K + ρ ∧
      (∀ b i, ‖d.normal b i‖ = 1) ∧ (∀ b i, ‖d.tangent b i‖ = 1) ∧
      (∀ b i, inner ℝ (d.tangent b i) (d.normal b i) = 0) ∧
      (∀ b i, |d.offset b i| ≤ T + r) ∧
      ∀ b i x, ‖x‖ ≤ T → x ∈ affineStrip (n b i) (β b i) r →
        x ∈ ⋃ j, affineStrip (d.normal b j) (d.offset b j) ((d.normalBudget : ℝ) * d.radius) :=
  exists_packed_strip_refinement_of_active μ (fun _ _ => inferInstance) n β hn hK hκ hε
    hr hT hρ hsmall hmass (fun b _ => hcap b) heps

/-- The same envelope controls the old slack, the reciprocal heavy-strip floor,
and every packing/list parameter. Empty raw families require no posterior. -/
theorem exists_envelope_strip_refinement_of_active {P : Type} {ι : P → Type}
    (μ : P → Measure StripSpace)
    (hprob : ∀ b, Nonempty (ι b) → IsProbabilityMeasure (μ b))
    (n : (b : P) → ι b → StripSpace) (β : (b : P) → ι b → ℝ)
    {K E ε r ρ : ℝ} (hn : ∀ b i, ‖n b i‖ = 1)
    (hK : 1 ≤ K) (hE : 1 ≤ E) (hKE : K ≤ E) (hε : 0 ≤ ε)
    (hr : 0 ≤ r) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hsmall : 4 * r ≤ ρ)
    (hmass : ∀ b i, E⁻¹ ≤ (μ b).real (boundedStrip (n b i) (β b i) r (2 * K)))
    (hcap : ∀ b, Nonempty (ι b) → ∀ x,
      (μ b) (Metric.closedBall x (32 * (1 + 2 * K) * r / ρ)) ≤ ENNReal.ofReal ε)
    (heps : 2 * ε ≤ (E⁻¹) ^ 2) :
    ∃ d : StripRefinement P, d.radius = ρ ∧ 0 < d.count ∧
      K ≤ (d.bins : ℝ) * d.radius ∧ (d.bins : ℝ) * d.radius ≤ 2 * E ∧
      (d.count : ℝ) ≤ 3 * E ^ 2 ∧ (d.normalBudget : ℝ) ≤ 5 * E ∧
      (∀ b i, ‖d.normal b i‖ = 1) ∧ (∀ b i, ‖d.tangent b i‖ = 1) ∧
      (∀ b i, inner ℝ (d.tangent b i) (d.normal b i) = 0) ∧
      (∀ b i, |d.offset b i| ≤ 3 * E) ∧
      ∀ b i x, ‖x‖ ≤ 2 * K → x ∈ affineStrip (n b i) (β b i) r →
        x ∈ ⋃ j, affineStrip (d.normal b j) (d.offset b j) ((d.normalBudget : ℝ) * d.radius) := by
  obtain ⟨d, hrad, _, hnormal, hcount, hc, hbins, hbinUpper, hn', he', hen, hβ, hcover⟩ :=
    exists_packed_strip_refinement_of_active μ hprob n β (K := K) (κ := E⁻¹) (T := 2 * K) hn (by linarith)
      (by positivity) hε hr (by linarith) hρ hsmall hmass hcap heps
  refine ⟨d, hrad, hcount, hbins, ?_, ?_, ?_, hn', he', hen, ?_, hcover⟩
  · exact hbinUpper.trans (by linarith)
  · have hE0 : E ≠ 0 := by linarith
    have hid : 2 / (E⁻¹) ^ 2 + 1 = 2 * E ^ 2 + 1 := by field_simp
    rw [hid] at hc
    linarith [one_le_pow₀ hE (n := 2)]
  · rw [hnormal]
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ 2 + 2 * K by linarith)
    linarith
  · intro b i
    exact (hβ b i).trans (by linarith)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
