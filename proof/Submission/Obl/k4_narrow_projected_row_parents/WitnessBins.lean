/- Adapted from this LOT tree o255, session x0901, branch x0901 at 7ca74bdb,
   Submission/Obl/k4_general_parent_narrow_contact_transfer/WitnessBins.lean.
   Earlier provenance comments in the source are retained. -/
import Mathlib
import Submission.Lib.K4ReferencePruning

/-!
# Witness velocity bins of retained states

After deleting states that are light relative to summable reference weights,
the velocity bins in which a retained state has positive mass carry palette
weight at least `δ / C`, where `C` is the constant of the velocity cap.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents.WitnessBins

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4ReferencePruning

noncomputable section

theorem witness_bins {Ω Q : Type*} [MeasurableSpace Ω] [MeasurableSpace Q]
    [MeasurableSingletonClass Q] [Countable Q]
    (ρ : Measure Ω) [IsFiniteMeasure ρ] (state : Ω → Q) (hstate : Measurable state)
    (vb : Ω → ℤ) (hvb : Measurable vb) (π' : Measure ℤ) (w : Q → ℝ≥0∞) (C δ : ℝ≥0∞)
    (hδ0 : δ ≠ 0) (hδtop : δ ≠ ⊤) (hC : C ≠ ⊤)
    (hcap : ∀ q (A : Set ℤ), MeasurableSet A →
      ρ {p | state p = q ∧ vb p ∈ A} ≤ C * w q * π' A)
    (q : Q) (hpos : 0 < (ρ.restrict (referenceKeep ρ state w δ)) (state ⁻¹' {q})) :
    δ / C ≤ π' {b | 0 < (ρ.restrict (referenceKeep ρ state w δ)) {p | state p = q ∧ vb p = b}} := by
  classical
  set ρ' := ρ.restrict (referenceKeep ρ state w δ) with hρ'
  set V : Set ℤ := {b | 0 < ρ' {p | state p = q ∧ vb p = b}} with hV
  have hrel := reference_pruned_palette_cap ρ state hstate vb π' w C δ hδ0 hδtop hcap q V
    (Set.to_countable V).measurableSet
  -- the state lives on the bins of `V`
  have hnull : ρ' {p | state p = q ∧ vb p ∉ V} = 0 := by
    have hsub : {p | state p = q ∧ vb p ∉ V} ⊆ ⋃ b ∈ Vᶜ, {p | state p = q ∧ vb p = b} := by
      intro p hp
      exact mem_iUnion₂.mpr ⟨vb p, hp.2, hp.1, rfl⟩
    refine measure_mono_null hsub ((measure_biUnion_null_iff (Set.to_countable _)).mpr ?_)
    intro b hb
    simp only [hV, mem_compl_iff, mem_setOf_eq, not_lt, nonpos_iff_eq_zero] at hb
    exact hb
  have hsplit : ρ' (state ⁻¹' {q}) ≤ ρ' {p | state p = q ∧ vb p ∈ V} := by
    have hcover : state ⁻¹' {q} ⊆ {p | state p = q ∧ vb p ∈ V} ∪
        {p | state p = q ∧ vb p ∉ V} := by
      intro p hp
      by_cases h : vb p ∈ V
      · left; exact ⟨hp, h⟩
      · right; exact ⟨hp, h⟩
    calc ρ' (state ⁻¹' {q}) ≤ ρ' ({p | state p = q ∧ vb p ∈ V} ∪
          {p | state p = q ∧ vb p ∉ V}) := measure_mono hcover
      _ ≤ ρ' {p | state p = q ∧ vb p ∈ V} + ρ' {p | state p = q ∧ vb p ∉ V} :=
          measure_union_le _ _
      _ = ρ' {p | state p = q ∧ vb p ∈ V} := by rw [hnull, add_zero]
  have hle : ρ' (state ⁻¹' {q}) ≤ C / δ * ρ' (state ⁻¹' {q}) * π' V := hsplit.trans hrel
  have hfin : ρ' (state ⁻¹' {q}) ≠ ⊤ := measure_ne_top _ _
  have h1 : 1 ≤ C / δ * π' V := by
    rw [mul_comm (C / δ) (ρ' (state ⁻¹' {q})), mul_assoc] at hle
    have hle' : ρ' (state ⁻¹' {q}) * 1 ≤ ρ' (state ⁻¹' {q}) * (C / δ * π' V) := by
      rw [mul_one]; exact hle
    exact (ENNReal.mul_le_mul_iff_right hpos.ne' hfin).mp hle'
  -- divide by `C / δ`
  by_cases hC0 : C = 0
  · exfalso
    subst hC0
    rw [ENNReal.zero_div, zero_mul] at h1
    exact absurd h1 (by simp)
  · have hCδ : C / δ ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hC0, hδtop⟩
    have hCδt : C / δ ≠ ⊤ := ENNReal.div_ne_top hC hδ0
    calc δ / C = (C / δ)⁻¹ := by rw [ENNReal.inv_div (Or.inl hδtop) (Or.inl hδ0)]
      _ = (C / δ)⁻¹ * 1 := by rw [mul_one]
      _ ≤ (C / δ)⁻¹ * (C / δ * π' V) := mul_le_mul_right h1 _
      _ = π' V := by rw [← mul_assoc, ENNReal.inv_mul_cancel hCδ hCδt, one_mul]

end

end Submission.Obl.k4_narrow_projected_row_parents.WitnessBins
