-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StateStripSaturation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StateStripSaturation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StateStripSaturation.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StateStripSaturation.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.StripSaturation

/-! Saturate every state under its ORIGINAL restricted law. The prediction
count is uniformly bounded, and the outside strip cap keeps the ORIGINAL
state denominator. The bounded-cover kernel is imported from x0706's
StripSaturation (d7f5ef00), in this LOT obligation. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips

abbrev UnitStripParameter := {p : StripSpace × ℝ // ‖p.1‖ = 1}

theorem exists_state_strip_saturation {Ω Z : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (state : Ω → Z)
    (hcell : ∀ e, MeasurableSet {z | state z = e})
    (U : Set Ω) (hU : MeasurableSet U) (V : Ω → StripSpace) (hV : Measurable V)
    (r θ : ℝ) (hθ : 0 < θ) :
    ∃ predictions : Z → Finset UnitStripParameter,
      (∀ e, ((predictions e).card : ℝ) ≤ θ⁻¹) ∧
      (∀ e, ∀ p ∈ predictions e,
        θ * μ.real {z | state z = e} <
          μ.real {z | state z = e ∧ z ∈ U ∧ V z ∈ affineStrip p.val.1 p.val.2 r}) ∧
      ∀ e (n : StripSpace) (β : ℝ), ‖n‖ = 1 →
        μ.real {z | state z = e ∧ z ∈ U ∧ V z ∈ affineStrip n β r ∧
          ∀ p ∈ predictions e, V z ∉ affineStrip p.val.1 p.val.2 r} ≤
            θ * μ.real {z | state z = e} := by
  classical
  let family := fun p : UnitStripParameter => U ∩ V ⁻¹' affineStrip p.val.1 p.val.2 r
  have hfamily (p : UnitStripParameter) : MeasurableSet (family p) :=
    hU.inter ((measurableSet_affineStrip _ _ _).preimage hV)
  have hex (e : Z) : ∃ s : Finset UnitStripParameter,
      (s.card : ℝ) ≤ θ⁻¹ ∧
      (∀ p ∈ s, θ * μ.real {z | state z = e} <
        μ.real {z | state z = e ∧ z ∈ U ∧ V z ∈ affineStrip p.val.1 p.val.2 r}) ∧
      ∀ p : UnitStripParameter,
        μ.real {z | state z = e ∧ z ∈ U ∧ V z ∈ affineStrip p.val.1 p.val.2 r ∧
          ∀ q ∈ s, V z ∉ affineStrip q.val.1 q.val.2 r} ≤
            θ * μ.real {z | state z = e} := by
    let Cell := {z | state z = e}
    let μe := μ.restrict Cell
    have hrestrict (D : Set Ω) (hD : MeasurableSet D) : μe.real D = μ.real (Cell ∩ D) := by
      change ((μ.restrict Cell) D).toReal = (μ (Cell ∩ D)).toReal
      rw [Measure.restrict_apply hD, inter_comm]
    by_cases hpos : 0 < μ.real Cell
    · obtain ⟨s, hcard, hheavy, hrest⟩ := bounded_original_heavy_cover μe family hfamily
        (mul_pos hθ hpos)
      have huniv : μe.real univ = μ.real Cell := by
        rw [hrestrict _ MeasurableSet.univ, inter_univ]
      refine ⟨s, ?_, ?_, ?_⟩
      · rw [huniv] at hcard
        have heq : μ.real Cell / (θ * μ.real Cell) = θ⁻¹ := by
          field_simp [hpos.ne', hθ.ne']
        exact hcard.trans_eq heq
      · intro p hp
        have h := hheavy p hp
        rw [hrestrict _ (hfamily p)] at h
        exact h
      · intro p
        have hUnion : MeasurableSet (⋃ q ∈ s, family q) :=
          Finset.measurableSet_biUnion s (fun q _ => hfamily q)
        have h := hrest p
        rw [hrestrict _ ((hfamily p).diff hUnion)] at h
        have heq : Cell ∩ (family p \ ⋃ q ∈ s, family q) =
            {z | state z = e ∧ z ∈ U ∧ V z ∈ affineStrip p.val.1 p.val.2 r ∧
              ∀ q ∈ s, V z ∉ affineStrip q.val.1 q.val.2 r} := by
          ext z
          constructor
          · rintro ⟨hze, ⟨hzU, hzstrip⟩, hzoutside⟩
            refine ⟨hze, hzU, hzstrip, ?_⟩
            intro q hq hzq
            exact hzoutside (mem_iUnion₂.mpr ⟨q, hq, hzU, hzq⟩)
          · rintro ⟨hze, hzU, hzstrip, hzoutside⟩
            refine ⟨hze, ⟨hzU, hzstrip⟩, ?_⟩
            intro hzunion
            obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.mp hzunion
            exact hzoutside q hq hzq.2
        rwa [heq] at h
    · have hz : μ.real Cell = 0 := le_antisymm (le_of_not_gt hpos) ENNReal.toReal_nonneg
      refine ⟨∅, by simp only [Finset.card_empty, Nat.cast_zero]; positivity, by simp, ?_⟩
      intro p
      have hzero : μ.real {z | state z = e ∧ z ∈ U ∧ V z ∈ affineStrip p.val.1 p.val.2 r ∧
          ∀ q ∈ (∅ : Finset UnitStripParameter), V z ∉ affineStrip q.val.1 q.val.2 r} = 0 :=
        measureReal_mono_null (fun _ h => h.1) hz
      rw [hzero, hz, mul_zero]
  choose predictions hcard hheavy hrest using hex
  refine ⟨predictions, hcard, hheavy, ?_⟩
  intro e n β hn
  exact hrest e ⟨(n, β), hn⟩

/-- Pad a uniformly bounded finite prediction set to a fixed finite array.
Every original prediction occurs; padding adds no coverage requirement. -/
theorem exists_prediction_array {I : Type*} (s : Finset I) (fallback : I) (J : ℕ)
    (hcard : s.card ≤ J) :
    ∃ p : Fin J → I, ∀ q ∈ s, ∃ j, p j = q := by
  classical
  let e := Fintype.equivFin ↥s
  let p := fun j : Fin J => if hj : j.val < s.card then
    ((e.symm ⟨j.val, by simpa only [Fintype.card_coe] using hj⟩ : ↥s) : I) else fallback
  refine ⟨p, ?_⟩
  intro q hq
  let v : ↥s := ⟨q, hq⟩
  let t := e v
  have ht : t.val < s.card := by simpa only [Fintype.card_coe] using t.isLt
  let j : Fin J := ⟨t.val, ht.trans_le hcard⟩
  refine ⟨j, ?_⟩
  dsimp only [p]
  rw [dif_pos ht]
  change ((e.symm (e v) : ↥s) : I) = q
  rw [e.symm_apply_apply]

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
