import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedSlices
import Submission.Obl.k4_general_wide_layer_offset_comparison.BasicFacts
import Submission.Obl.k4_general_wide_layer_offset_comparison.OriginalBudgets
import Submission.Obl.k4_scalar_capped_heavy_potential.PositiveCodes
import Submission.Obl.k4_critical_conditional_row_preparation.Pruning

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ActiveProjectedSlices.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace ProjectedLayer

variable {α : Type} [MeasurableSpace α]

/-- Literal original domain slices after removing only the conull clipping
and time exceptions. -/
def goodSliceEvent (L : ProjectedLayer α) (p : Parent α) (k : ℕ) (h g b : ℝ)
    (D : Fin L.count → Finset (ℤ × ℤ × ℤ)) (e : SliceIndex D) : Set (α × ℝ) :=
  L.slicedEvent p k h g b D e ∩ p.baseGood k

/-- Active indices retain the original layer identity and integer domain;
activity is tested using the unchanged current original-source measure. -/
abbrev ActiveSlice (L : ProjectedLayer α) (p : Parent α) (k : ℕ) (h g b : ℝ)
    (D : Fin L.count → Finset (ℤ × ℤ × ℤ)) (σ : Measure (α × ℝ)) :=
  {e : SliceIndex D // σ (L.goodSliceEvent p k h g b D e) ≠ 0}

theorem goodSliceEvent_disjoint (L : ProjectedLayer α) (p : Parent α)
    {k : ℕ} {h g b : ℝ} (D : Fin L.count → Finset (ℤ × ℤ × ℤ))
    (hdisj : Pairwise (fun e f =>
      Disjoint (L.slicedEvent p k h g b D e) (L.slicedEvent p k h g b D f))) :
    Pairwise (fun e f =>
      Disjoint (L.goodSliceEvent p k h g b D e) (L.goodSliceEvent p k h g b D f)) := by
  intro e f hef
  exact (hdisj hef).mono inter_subset_left inter_subset_left

/-- The actual finite domain atlas remains a cover after discarding null
original slices. No mass normalization or selection of a new source law occurs. -/
theorem exists_active_slices (L : ProjectedLayer α) (p : Parent α) (hbase : p.Basic)
    {k : ℕ} {s m H h g b : ℝ} (hL : L.Valid p k s m H) (hH : 1 ≤ H)
    (hh : 0 < h) (hh1 : h ≤ 1) (hb : 0 < b) (hbβ : b ≤ L.β) (hβg : L.β ≤ g)
    (σ : Measure (α × ℝ)) (hσ : σ ≤ p.ρ k) (hcover : L.Covers σ) :
    ∃ D : Fin L.count → Finset (ℤ × ℤ × ℤ),
      (∀ e, MeasurableSet (L.goodSliceEvent p k h g b D e)) ∧
      Pairwise (fun e f =>
        Disjoint (L.goodSliceEvent p k h g b D e) (L.goodSliceEvent p k h g b D f)) ∧
      (∀ᵐ ω ∂σ, ∃ e : L.ActiveSlice p k h g b D σ,
        ω ∈ L.goodSliceEvent p k h g b D e.val) ∧
      (∑ e : SliceIndex D, L.slicedWeight p k s m h b e.1) ≤ 240 * H ^ 3 := by
  classical
  obtain ⟨D, hD, hdisj, hc, hbudget⟩ :=
    L.exists_disjoint_slices p hbase hL hH hh hh1 hb hbβ hβg σ hσ hcover
  let E := L.goodSliceEvent p k h g b D
  have hE (e : SliceIndex D) : MeasurableSet (E e) :=
    (hD e).inter (Parent.Basic.measurableSet_baseGood p hbase k)
  have hEd := L.goodSliceEvent_disjoint p D hdisj
  have hgood : ∀ᵐ ω ∂σ, ω ∈ p.baseGood k :=
    (Parent.Basic.ae_baseGood p hbase k).filter_mono (ae_mono (hσ.trans (hbase k).2.2.2.2.1))
  have hactive : ∀ᵐ ω ∂σ, ∃ e : L.ActiveSlice p k h g b D σ, ω ∈ E e.val := by
    letI : MeasurableSpace (SliceIndex D) := ⊤
    letI : MeasurableSpace (Option (SliceIndex D)) := ⊤
    let label := Submission.Obl.k4_critical_conditional_row_preparation.coverLabel E
    let F : Finset (Option (SliceIndex D)) :=
      Finset.univ.filter (fun e => σ {ω | label ω = e} ≠ 0)
    have hm : Measurable label :=
      Submission.Obl.k4_critical_conditional_row_preparation.measurable_coverLabel E hE hEd
    have hpF := Submission.Obl.k4_scalar_capped_heavy_potential.ae_mem_finite_positive_codes
      σ label hm F (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩)
    have hpos : ∀ᵐ ω ∂σ, σ {ω' | label ω' = label ω} ≠ 0 := by
      filter_upwards [hpF] with ω hω
      exact (Finset.mem_filter.mp hω).2
    filter_upwards [hc, hgood, hpos] with ω hω hgω hpω
    obtain ⟨e, he⟩ := hω
    have heE : ω ∈ E e := ⟨he, hgω⟩
    have hlabel : Submission.Obl.k4_critical_conditional_row_preparation.coverLabel E ω = some e :=
      (Submission.Obl.k4_critical_conditional_row_preparation.coverLabel_eq_some E hEd ω e).mpr heE
    have heq : {ω' | Submission.Obl.k4_critical_conditional_row_preparation.coverLabel E ω' =
        Submission.Obl.k4_critical_conditional_row_preparation.coverLabel E ω} = E e := by
      ext ω'
      rw [hlabel]
      exact Submission.Obl.k4_critical_conditional_row_preparation.coverLabel_eq_some E hEd ω' e
    rw [heq] at hpω
    exact ⟨⟨e, hpω⟩, heE⟩
  exact ⟨D, hE, hEd, hactive, hbudget⟩

/-- A retained original source forces positivity of its original velocity
palette bin; a zero bin could not have carried this slice. -/
theorem activeSlice_palette_positive (L : ProjectedLayer α) (p : Parent α) (hbase : p.Basic)
    {k : ℕ} {s m H h g b t R : ℝ} (hL : L.Valid p k s m H)
    (hat : p.AtDepth k t R) (hK : 0 ≤ p.K k) (hmlo : R⁻¹ ≤ m) (hmhi : m ≤ R)
    (D : Fin L.count → Finset (ℤ × ℤ × ℤ))
    (σ : Measure (α × ℝ)) (hσ : σ ≤ p.μ k) (e : L.ActiveSlice p k h g b D σ) :
    0 < p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = L.tag e.val.1 0} := by
  apply bot_lt_iff_ne_bot.mpr
  intro hzero
  apply e.property
  exact hat.palette_null_source p hbase hK hmlo hmhi _ hzero σ hσ _ (by
    intro ω hω
    have hc := L.slicedEvent_code p hL D e.val hω.1
    have hh := congrArg (fun c => c.1 0) hc
    exact hh)

/-- Removing null entries cannot increase the full original reference
budget, including when the surviving entries have very unequal masses. -/
theorem activeSlice_reference_budget (L : ProjectedLayer α) (p : Parent α)
    {k : ℕ} {s m H h g b : ℝ} (D : Fin L.count → Finset (ℤ × ℤ × ℤ))
    (σ : Measure (α × ℝ))
    (hbudget : (∑ e : SliceIndex D, L.slicedWeight p k s m h b e.1) ≤ 240 * H ^ 3) :
    (∑ e : L.ActiveSlice p k h g b D σ,
      L.slicedWeight p k s m h b e.val.1) ≤ 240 * H ^ 3 := by
  classical
  apply le_trans ?_ hbudget
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun e : SliceIndex D => σ (L.goodSliceEvent p k h g b D e) ≠ 0))
    (by simp) (fun e : SliceIndex D => L.slicedWeight p k s m h b e.1)]
  exact Finset.sum_le_univ_sum_of_nonneg (fun _ => ENNReal.toReal_nonneg)

end ProjectedLayer
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
