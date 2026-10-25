-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripStateMass, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripStateMass.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripStateMass.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripStateMass.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripStateMass.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripDomination

/-! Countable narrow-state selections retain their stated fraction of the
original state masses. No selected posterior denominator appears. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open Set MeasureTheory
open Submission.Lib.K4VelocityStrips

/-- The same original relative floor sums over cells that are disjoint up to
null sets. In particular, shared endpoints of old time blocks cost nothing. -/
theorem aedisjoint_cell_relative_mass {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) (F G : I → Set Ω) (hF : ∀ i, NullMeasurableSet (F i) μ)
    (hG : ∀ i, NullMeasurableSet (G i) μ)
    (hdisj : Pairwise (fun i j => AEDisjoint μ (F i) (F j)))
    (hsub : ∀ i, G i ⊆ F i) (θ : ENNReal) (hfloor : ∀ i, θ * μ (F i) ≤ μ (G i)) :
    θ * μ (⋃ i, F i) ≤ μ (⋃ i, G i) := by
  have hdisjG : Pairwise (fun i j => AEDisjoint μ (G i) (G j)) :=
    fun i j hij => (hdisj hij).mono (hsub i) (hsub j)
  rw [measure_iUnion₀ hdisj hF, measure_iUnion₀ hdisjG hG, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum hfloor

theorem countable_cell_relative_mass {Ω Z : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Z] [Countable Z] [MeasurableSingletonClass Z]
    (μ : Measure Ω) (q : Ω → Z) (hq : Measurable q) (Bad : Set Z)
    (G : Z → Set Ω) (hG : ∀ z, MeasurableSet (G z))
    (hfiber : ∀ z, G z ⊆ q ⁻¹' {z}) (θ : ENNReal)
    (hfloor : ∀ z ∈ Bad, θ * μ (q ⁻¹' {z}) ≤ μ (G z)) :
    θ * μ (q ⁻¹' Bad) ≤ μ (⋃ z : Bad, G z) := by
  have hsum : (∑' z : Bad, μ (q ⁻¹' {(z : Z)})) = μ (q ⁻¹' Bad) :=
    tsum_measure_preimage_singleton (Set.to_countable Bad)
      (fun z _ => (measurableSet_singleton z).preimage hq)
  have hdisj : Pairwise (fun a b : Bad => Disjoint (G a) (G b)) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro x hx hy
    apply hab
    apply Subtype.ext
    exact (hfiber a hx).symm.trans (hfiber b hy)
  calc
    _ = θ * ∑' z : Bad, μ (q ⁻¹' {(z : Z)}) := by rw [hsum]
    _ = ∑' z : Bad, θ * μ (q ⁻¹' {(z : Z)}) := ENNReal.tsum_mul_left.symm
    _ ≤ ∑' z : Bad, μ (G z) := ENNReal.tsum_le_tsum (fun z => hfloor z z.property)
    _ = _ := (measure_iUnion hdisj (fun z => hG z)).symm

def narrowStateUnion {Ω Z : Type*} (q : Ω → Z) (U : Set Ω)
    (V : Ω → StripSpace) (n : Z → StripSpace) (β : Z → ℝ) (r : ℝ) (Bad : Set Z) : Set Ω :=
  ⋃ z : Bad, {x | q x = z ∧ x ∈ U ∧ V x ∈ affineStrip (n z) (β z) r}

theorem measurableSet_narrowStateUnion {Ω Z : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Z] [Countable Z] [MeasurableSingletonClass Z]
    (q : Ω → Z) (hq : Measurable q) (U : Set Ω) (hU : MeasurableSet U)
    (V : Ω → StripSpace) (hV : Measurable V) (n : Z → StripSpace) (β : Z → ℝ)
    (r : ℝ) (Bad : Set Z) : MeasurableSet (narrowStateUnion q U V n β r Bad) := by
  apply MeasurableSet.iUnion
  intro z
  exact ((measurableSet_singleton (z : Z)).preimage hq).inter
    (hU.inter ((measurableSet_affineStrip _ _ _).preimage hV))

theorem narrowStateUnion_subset {Ω Z : Type*} (q : Ω → Z) (U : Set Ω)
    (V : Ω → StripSpace) (n : Z → StripSpace) (β : Z → ℝ) (r : ℝ) (Bad : Set Z) :
    narrowStateUnion q U V n β r Bad ⊆ U := by
  intro x hx
  obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hx
  exact hz.2.1

theorem narrowStateUnion_mass {Ω Z : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Z] [Countable Z] [MeasurableSingletonClass Z]
    (μ : Measure Ω) (q : Ω → Z) (hq : Measurable q) (U : Set Ω) (hU : MeasurableSet U)
    (V : Ω → StripSpace) (hV : Measurable V) (n : Z → StripSpace) (β : Z → ℝ)
    (r : ℝ) (Bad : Set Z) (θ : ENNReal)
    (hfloor : ∀ z ∈ Bad, θ * μ {x | q x = z} ≤
      μ {x | q x = z ∧ x ∈ U ∧ V x ∈ affineStrip (n z) (β z) r}) :
    θ * μ (q ⁻¹' Bad) ≤ μ (narrowStateUnion q U V n β r Bad) := by
  apply countable_cell_relative_mass μ q hq Bad
    (fun z => {x | q x = z ∧ x ∈ U ∧ V x ∈ affineStrip (n z) (β z) r})
    (fun z => ((measurableSet_singleton z).preimage hq).inter
      (hU.inter ((measurableSet_affineStrip _ _ _).preimage hV)))
    (fun z x hx => hx.1) θ hfloor

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
