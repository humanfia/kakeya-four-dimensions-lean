-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.FiniteMergedPrediction, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/FiniteMergedPrediction.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/FiniteMergedPrediction.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/FiniteMergedPrediction.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeMergedPrediction
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripMergedMass

/-! A uniformly finite list of predicted strips per original fine packet.
The terminal observation list pays the prediction count, independently of
the size of the old-posterior heavy net. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface
open scoped BigOperators RealInnerProductSpace

namespace FiniteMergedPrediction

variable {W : ℕ} {p : PathData W} {i J : ℕ}
    (d : StripRefinement (p.StripLevel i))
    (rawNormal : Fin J → p.StripLevel i → Fin p.C → StripSpace)
    (rawOffset : Fin J → p.StripLevel i → Fin p.C → ℝ)

open Classical in
def parameterList (m : ℕ) (w : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
    Finset d.MergedParameterLabel :=
  Finset.univ.biUnion (fun t => NativeMergedPrediction.parameterList d (rawNormal t) (rawOffset t) m w o)

def success (m stop : ℕ) (b : p.StripLevel i) (code : StripParameterCode) :
    Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  ⋃ t : Fin J, NativeMergedPrediction.success d (rawNormal t) (rawOffset t) m stop b code

section Path

variable {N L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

theorem parameterList_card
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (w : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
    ((parameterList d rawNormal rawOffset m w o).card : ℝ) ≤
      (J : ℝ) * (250 * ((m : ℝ) * p.κ) ^ 2) := by
  classical
  calc
    _ ≤ ((∑ t : Fin J, (NativeMergedPrediction.parameterList d (rawNormal t) (rawOffset t) m w o).card : ℕ) : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le :
        (parameterList d rawNormal rawOffset m w o).card ≤
          ∑ t : Fin J, (NativeMergedPrediction.parameterList d (rawNormal t) (rawOffset t) m w o).card)
    _ = ∑ t : Fin J, ((NativeMergedPrediction.parameterList d (rawNormal t) (rawOffset t) m w o).card : ℝ) := by simp
    _ ≤ ∑ _t : Fin J, 250 * ((m : ℝ) * p.κ) ^ 2 :=
      Finset.sum_le_sum (fun t _ => NativeMergedPrediction.parameterList_card d (rawNormal t) (rawOffset t) hp w o)
    _ = _ := by simp

theorem measurableSet_success
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (stop : ℕ) (b : p.StripLevel i) (code : StripParameterCode) :
    MeasurableSet (success d rawNormal rawOffset m stop b code) :=
  MeasurableSet.iUnion (fun t => NativeMergedPrediction.measurableSet_success d (rawNormal t) (rawOffset t) hp stop b code)

theorem success_section_format
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hN : 2 ≤ N)
    (stop : ℕ) (b : p.StripLevel i) (code : StripParameterCode) (copy : ℕ) :
    gfmt 7 ((J : ℝ) * N ^ (4 * Mp + 2)) Dp
      {z : Fin 7 → ℝ | ((copy, fun j : Fin 6 => z j.castSucc), z 6) ∈
        success d rawNormal rawOffset m stop b code} := by
  have h := Submission.Lib.K4RepresentativeAssembly.fmt_iUnion
    (fun t : Fin J => {z : Fin 7 → ℝ | ((copy, fun j : Fin 6 => z j.castSucc), z 6) ∈
      NativeMergedPrediction.success d (rawNormal t) (rawOffset t) m stop b code})
    (fun t => NativeMergedPrediction.success_section_format_power d (rawNormal t) (rawOffset t) hp hN stop b code copy)
  convert h using 1
  ext z
  simp only [success, mem_ofPred_eq, mem_iUnion]

theorem merged_parameter_known
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (stop : ℕ) (width aL : ℝ) (haL : aL = δ N L)
    (a : d.MergedLabel) (x : (ℕ × (Fin 6 → ℝ)) × ℝ)
    (hx : x ∈ d.mergedIncidence (p.stripParent i) width
      (success d rawNormal rawOffset m stop) a) :
    d.mergedParameterLabel a ∈ parameterList d rawNormal rawOffset m
      (p.stripParent i a.1).world (gobs (B (p.stripParent i a.1).world) aL x) := by
  classical
  obtain ⟨t, ht⟩ := mem_iUnion.mp hx.2
  exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _,
    NativeMergedPrediction.merged_parameter_known d (rawNormal t) (rawOffset t) hp
      stop width aL haL a x ⟨hx.1, ht⟩⟩

/-- All captured strips in all passes are covered by ONE disjoint merged
atlas. The success predicates remember the old fine packet and one of its
uniformly many original predictions. -/
theorem original_residual_covered
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (stop : ℕ) {width r₀ r₁ : ℝ} (hr : 0 < d.radius)
    (hn : ∀ b j, ‖d.normal b j‖ = 1)
    (hbins : p.κ ≤ (d.bins : ℝ) * d.radius)
    (hmeshes : r₁ ≤ d.radius) (hrawWidth : r₀ + (1 + 2 * p.κ) * r₁ ≤ width)
    (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hcover : ∀ w, H w ⊆ {x | ∃ (b : p.StripLevel i) (a : Fin p.C) (t : Fin J),
      p.γ b = w ∧ x ∈ (p.stripParent i b).incidences ∧
      x ∈ p.packetWitness m stop (p.γ b) a ∧
      packetVelocity (((2 : ℝ) ^ p.T i)⁻¹) (p.stripParent i b).frame
        (p.stripParent i b).velocity x.1 ∈ affineStrip (rawNormal t b a) (rawOffset t b a) r₀ ∧
      (∃ j, stripParametersClose (rawNormal t b a) (rawOffset t b a)
        (d.normal b j) (d.offset b j) r₁) ∧
      packetVelocity (((2 : ℝ) ^ p.T i)⁻¹) (p.stripParent i b).frame
        (p.stripParent i b).velocity x.1 ∉
          stripFarOverlap (d.normal b) (d.offset b) width d.radius (2 * p.κ)}) :
    ∀ w, H w ⊆ {x | ∃ a : d.MergedLabel,
      (p.stripParent i a.1).world = w ∧ x ∈ d.mergedIncidence (p.stripParent i) width
        (success d rawNormal rawOffset m stop) a} := by
  apply d.original_residual_covered_by_merged_incidence (p.stripParent i)
    (hp.stripParent_valid i) hr hn hbins
  intro w x hx
  obtain ⟨b, a, t, hγ, hxold, hxf, hraw, hnet, hgood⟩ := hcover w hx
  have hbound := hp.stripParent_velocity_bound i b x.1
    ((hp.stripParent_valid i b).2.2.2.2.2.2.2.2.2.2.1 x hxold).2.1
  refine ⟨b, hγ, hxold, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := hnet
    exact mem_iUnion.mpr ⟨j,
      (affineStrip_mem_of_close_parameters_mod_sign (by linarith [hp.1]) hbound hj hraw).trans hrawWidth⟩
  · intro q hq
    have hcode := mergedStripCell_code_predicted hr hmeshes (by linarith [hp.1]) hbound
      hraw hnet hrawWidth hq hgood
    exact mem_iUnion.mpr ⟨t, a, hcode, hxf⟩

end Path

end FiniteMergedPrediction

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
