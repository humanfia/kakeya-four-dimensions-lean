import Submission.Obl.k4_general_wide_layer_offset_comparison.SelectedProjectedSlices

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ProjectedSourceAtlas.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

namespace ProjectedLayer

variable {α : Type} [MeasurableSpace α]

/-- The finite source atlas constructed from one literal projected layer.
Its source law, bins, domains and reference weights all remain original. -/
structure SourceAtlas (A : ProjectedLayer α) (p : Parent α) (k : ℕ) (s m H h g b : ℝ)
    (σ : Measure (α × ℝ)) where
  valid : A.Valid p k s m H
  domains : Fin A.count → Finset (ℤ × ℤ × ℤ)
  measurable_event : ∀ e, MeasurableSet (A.goodSliceEvent p k h g b domains e)
  disjoint_event : Pairwise (fun e f =>
    Disjoint (A.goodSliceEvent p k h g b domains e) (A.goodSliceEvent p k h g b domains f))
  cover : ∀ᵐ ω ∂σ, ∃ e : A.ActiveSlice p k h g b domains σ,
    ω ∈ A.goodSliceEvent p k h g b domains e.val
  palette_positive : ∀ e : A.ActiveSlice p k h g b domains σ,
    0 < p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = A.tag e.val.1 0}
  reference_budget : (∑ e : SliceIndex domains, A.slicedWeight p k s m h b e.1) ≤ 240 * H ^ 3

/-- Actual wide-layer geometry and the prepared parent's original palette
supply the whole source atlas, rather than assuming a new density law. -/
theorem exists_sourceAtlas (A : ProjectedLayer α) (p : Parent α) (hbase : p.Basic)
    {k : ℕ} {s m H h g b t R : ℝ} (hA : A.Valid p k s m H) (hH : 1 ≤ H)
    (hh : 0 < h) (hh1 : h ≤ 1) (hb : 0 < b) (hbβ : b ≤ A.β) (hβg : A.β ≤ g)
    (hat : p.AtDepth k t R) (hK : 0 ≤ p.K k) (hmlo : R⁻¹ ≤ m) (hmhi : m ≤ R)
    (σ : Measure (α × ℝ)) (hσ : σ ≤ p.ρ k) (hc : A.Covers σ) :
    Nonempty (A.SourceAtlas p k s m H h g b σ) := by
  obtain ⟨D, hD, hd, hcover, hbudget⟩ :=
    A.exists_active_slices p hbase hA hH hh hh1 hb hbβ hβg σ hσ hc
  exact ⟨{
    valid := hA
    domains := D
    measurable_event := hD
    disjoint_event := hd
    cover := hcover
    palette_positive := A.activeSlice_palette_positive p hbase hA hat hK hmlo hmhi
      D σ (hσ.trans (hbase k).2.2.2.2.1)
    reference_budget := hbudget }⟩

namespace SourceAtlas

variable {A : ProjectedLayer α} {p : Parent α} {k : ℕ} {s m H h g b : ℝ}
    {σ : Measure (α × ℝ)} (f : A.SourceAtlas p k s m H h g b σ)

abbrev Index := Option (A.ActiveSlice p k h g b f.domains σ)

def selector : α × ℝ → f.Index := A.selectedSlice p k h g b f.domains σ

def key (i : f.Index) : Option ComparisonCode :=
  i.map (fun e => A.sliceComparisonCode e.val)

def polynomial : f.Index → MvPolynomial (Fin 3) ℝ
  | none => 0
  | some e => A.sliceChart h g b e.val

def sheet (i : f.Index) : EuclideanSpace ℂ (Fin 3) → ℂ :=
  polynomialMatchSheet (f.polynomial i)

theorem degree (i : f.Index) : (f.polynomial i).totalDegree ≤ 2 := by
  cases i with
  | none => simp [polynomial]
  | some e => exact A.sliceChart_degree p f.valid e.val

theorem isMatchSheet (i : f.Index) :
    Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.IsMatchSheet (f.sheet i) :=
  polynomialMatchSheet_isMatchSheet _ (f.degree i)

theorem atom_measurable (i : f.Index) : MeasurableSet {ω | f.selector ω = i} :=
  A.selectedSlice_atom_measurable p f.domains σ f.measurable_event f.disjoint_event i

theorem key_ae : ∀ᵐ ω ∂σ,
    f.key (f.selector ω) = some (p.comparisonCode k m h g b ω) :=
  A.selectedSlice_code p f.valid f.domains σ f.disjoint_event f.cover

theorem selected_source_ae : ∀ᵐ ω ∂σ, ∃ e : A.ActiveSlice p k h g b f.domains σ,
    f.selector ω = some e ∧ ω ∈ A.goodSliceEvent p k h g b f.domains e.val := by
  filter_upwards [f.cover] with ω hω
  obtain ⟨e, he⟩ := hω
  exact ⟨e, (A.selectedSlice_some_iff p f.domains σ f.disjoint_event ω e).mpr he, he⟩

theorem off_cover_null : σ {ω | f.selector ω = none} = 0 := by
  have hne : ∀ᵐ ω ∂σ, f.selector ω ≠ none := by
    filter_upwards [f.selected_source_ae] with ω hω
    obtain ⟨e, he, -⟩ := hω
    rw [he]
    exact Option.some_ne_none e
  simpa only [not_not] using ae_iff.mp hne

theorem prior_budget (hbase : p.Basic) (hN : 1 ≤ p.N k) (hs : 0 ≤ s) (hd : 0 ≤ p.d)
    (hh : 0 < h) (hb : 0 < b) :
    (∑ i : f.Index, p.comparisonPrior k s m h b (f.key i)) ≤ 1 + 240 * H ^ 3 :=
  A.comparisonPrior_active_budget p hbase hN hs hd hh hb f.domains σ
    f.palette_positive f.reference_budget

end SourceAtlas
end ProjectedLayer
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
