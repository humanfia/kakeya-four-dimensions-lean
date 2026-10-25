import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedComparisonPriors
import Submission.Obl.k4_general_wide_layer_offset_comparison.PolynomialMatchSheets
import Submission.Obl.k4_general_wide_layer_offset_comparison.SourceResolution

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/SelectedProjectedSlices.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

noncomputable section

namespace ProjectedLayer

variable {α : Type} [MeasurableSpace α]

def selectedSlice (L : ProjectedLayer α) (p : Parent α) (k : ℕ) (h g b : ℝ)
    (D : Fin L.count → Finset (ℤ × ℤ × ℤ)) (σ : Measure (α × ℝ)) :
    α × ℝ → Option (L.ActiveSlice p k h g b D σ) :=
  Submission.Obl.k4_critical_conditional_row_preparation.coverLabel
    (fun e => L.goodSliceEvent p k h g b D e.val)

theorem activeSlice_disjoint (L : ProjectedLayer α) (p : Parent α)
    {k : ℕ} {h g b : ℝ} (D : Fin L.count → Finset (ℤ × ℤ × ℤ))
    (σ : Measure (α × ℝ))
    (hd : Pairwise (fun e f =>
      Disjoint (L.goodSliceEvent p k h g b D e) (L.goodSliceEvent p k h g b D f))) :
    Pairwise (fun e f : L.ActiveSlice p k h g b D σ =>
      Disjoint (L.goodSliceEvent p k h g b D e.val) (L.goodSliceEvent p k h g b D f.val)) := by
  intro e f hef
  exact hd (fun heq => hef (Subtype.ext heq))

theorem selectedSlice_some_iff (L : ProjectedLayer α) (p : Parent α)
    {k : ℕ} {h g b : ℝ} (D : Fin L.count → Finset (ℤ × ℤ × ℤ))
    (σ : Measure (α × ℝ))
    (hd : Pairwise (fun e f =>
      Disjoint (L.goodSliceEvent p k h g b D e) (L.goodSliceEvent p k h g b D f)))
    (ω : α × ℝ) (e : L.ActiveSlice p k h g b D σ) :
    L.selectedSlice p k h g b D σ ω = some e ↔ ω ∈ L.goodSliceEvent p k h g b D e.val :=
  Submission.Obl.k4_critical_conditional_row_preparation.coverLabel_eq_some _
    (L.activeSlice_disjoint p D σ hd) ω e

/-- Every atom of the actual finite original-label selector is measurable,
including its off-cover value. No measurable structure on trajectories beyond
the one in the frozen hypotheses is required. -/
theorem selectedSlice_atom_measurable (L : ProjectedLayer α) (p : Parent α)
    {k : ℕ} {h g b : ℝ} (D : Fin L.count → Finset (ℤ × ℤ × ℤ))
    (σ : Measure (α × ℝ)) (hE : ∀ e, MeasurableSet (L.goodSliceEvent p k h g b D e))
    (hd : Pairwise (fun e f =>
      Disjoint (L.goodSliceEvent p k h g b D e) (L.goodSliceEvent p k h g b D f)))
    (i : Option (L.ActiveSlice p k h g b D σ)) :
    MeasurableSet {ω | L.selectedSlice p k h g b D σ ω = i} := by
  classical
  cases i with
  | some e =>
    have heq : {ω | L.selectedSlice p k h g b D σ ω = some e} =
        L.goodSliceEvent p k h g b D e.val := by
      ext ω
      exact L.selectedSlice_some_iff p D σ hd ω e
    rw [heq]
    exact hE e.val
  | none =>
    have heq : {ω | L.selectedSlice p k h g b D σ ω = none} =
        (⋃ e : L.ActiveSlice p k h g b D σ, L.goodSliceEvent p k h g b D e.val)ᶜ := by
      ext ω
      simpa only [selectedSlice, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion] using
        (Submission.Obl.k4_critical_conditional_row_preparation.coverLabel_eq_none
          (fun e : L.ActiveSlice p k h g b D σ => L.goodSliceEvent p k h g b D e.val) ω)
    rw [heq]
    exact (MeasurableSet.iUnion
      (fun e : L.ActiveSlice p k h g b D σ => hE e.val)).compl

/-- The selected comparison key is the actual observable original key
almost everywhere, independently of the projected layer. -/
theorem selectedSlice_code (L : ProjectedLayer α) (p : Parent α)
    {k : ℕ} {s m H h g b : ℝ} (hL : L.Valid p k s m H)
    (D : Fin L.count → Finset (ℤ × ℤ × ℤ)) (σ : Measure (α × ℝ))
    (hd : Pairwise (fun e f =>
      Disjoint (L.goodSliceEvent p k h g b D e) (L.goodSliceEvent p k h g b D f)))
    (hc : ∀ᵐ ω ∂σ, ∃ e : L.ActiveSlice p k h g b D σ,
      ω ∈ L.goodSliceEvent p k h g b D e.val) :
    ∀ᵐ ω ∂σ, (L.selectedSlice p k h g b D σ ω).map (fun e => L.sliceComparisonCode e.val) =
      some (p.comparisonCode k m h g b ω) := by
  filter_upwards [hc] with ω hω
  obtain ⟨e, he⟩ := hω
  rw [(L.selectedSlice_some_iff p D σ hd ω e).mpr he, Option.map_some]
  exact congrArg some (L.slicedEvent_code p hL D e.val he.1).symm

/-- The chart polynomial attached to an actual original domain. -/
def sliceChart (L : ProjectedLayer α) (h g b : ℝ)
    {D : Fin L.count → Finset (ℤ × ℤ × ℤ)} (e : SliceIndex D) :
    MvPolynomial (Fin 3) ℝ :=
  projectedChartPolynomial (L.G e.1) (domainTime h e.2.val) (32 * h)
    (domainIntercept h g b e.2.val) (domainVelocity g e.2.val) (32 * b)

theorem sliceChart_degree (L : ProjectedLayer α) (p : Parent α)
    {k : ℕ} {s m H h g b : ℝ} (hL : L.Valid p k s m H)
    {D : Fin L.count → Finset (ℤ × ℤ × ℤ)} (e : SliceIndex D) :
    (L.sliceChart h g b e).totalDegree ≤ 2 :=
  projectedChartPolynomial_degree _ ((hL.2.2.2.2.2.1 e.1).2.1) _ _ _ _ _

/-- On the unchanged original source event, its selected chart recovers
its original projected predictor exactly. -/
theorem sliceChart_recover (L : ProjectedLayer α) (p : Parent α)
    {k : ℕ} {s m H h g b : ℝ} (hL : L.Valid p k s m H)
    (hh : 0 < h) (hb : 0 < b)
    {D : Fin L.count → Finset (ℤ × ℤ × ℤ)} (e : SliceIndex D)
    {ω : α × ℝ} (hω : ω ∈ L.goodSliceEvent p k h g b D e) (z : Fin 3 → ℝ)
    (hz : ∀ i : Fin 2, z i.castSucc = p.normalizedDomainBase k h g b ω i) :
    eval z (L.sliceChart h g b e) = eval ![ω.2, (p.x k ω.1 ω.2) 2] (L.G e.1) := by
  have hcode := congrArg Prod.snd (L.slicedEvent_code p hL D e hω.1)
  have hbase := p.normalizedDomainBase_on_code hcode
  apply projectedChartPolynomial_recover _ (by positivity) (by positivity)
    ![ω.2, (p.x k ω.1 ω.2) 1, (p.x k ω.1 ω.2) 2] z
  · simpa only [Fin.castSucc_zero, projectedDomainCoordinates, Matrix.cons_val_zero] using (hz 0).trans (congrFun hbase 0)
  · simpa only [show (1 : Fin 2).castSucc = (1 : Fin 3) from rfl,
      projectedDomainCoordinates, Matrix.cons_val_one, Matrix.cons_val_zero] using
      (hz 1).trans (congrFun hbase 1)

/-- The native signal stays at the original incidence. Only the projected
chart will be evaluated at a later jittered matching point. -/
theorem sliceChart_native_fit (L : ProjectedLayer α) (p : Parent α)
    {k : ℕ} {s m H h g b : ℝ} (hL : L.Valid p k s m H)
    (hh : 0 < h) (hb : 0 < b)
    {D : Fin L.count → Finset (ℤ × ℤ × ℤ)} (e : SliceIndex D)
    {ω : α × ℝ} (hω : ω ∈ L.goodSliceEvent p k h g b D e) (z : Fin 3 → ℝ)
    (hz : ∀ i : Fin 2, z i.castSucc = p.normalizedDomainBase k h g b ω i) :
    |eval z (L.sliceChart h g b e) - eval (p.x k ω.1 ω.2) (p.P k)| ≤ H * p.N k ^ (-s) := by
  rw [L.sliceChart_recover p hL hh hb e hω z hz, abs_sub_comm]
  exact L.slicedEvent_fit p hL D e hω.1

/-- Positive original source mass supplies a point witnessing all fixed
physical anchor bounds of the stored integer domain and major bin. -/
theorem activeSlice_anchor_bounds (L : ProjectedLayer α) (p : Parent α)
    {k : ℕ} {s m H h g b : ℝ} (hL : L.Valid p k s m H)
    (hN : 0 < p.N k) (hh : 0 < h) (hg : 0 < g) (hb : 0 < b)
    {D : Fin L.count → Finset (ℤ × ℤ × ℤ)} (σ : Measure (α × ℝ))
    (e : L.ActiveSlice p k h g b D σ) :
    0 ≤ domainTime h e.val.2.val ∧ domainTime h e.val.2.val ≤ 1 ∧
      |domainVelocity g e.val.2.val| ≤ p.K k + g ∧
      |(L.tag e.val.1 0 : ℝ) * p.N k ^ (-m)| ≤ p.K k + p.N k ^ (-m) := by
  obtain ⟨ω, hω⟩ := nonempty_of_measure_ne_zero e.property
  have hc := L.slicedEvent_code p hL D e.val hω.1
  have hdomain : p.domainCode k h g b ω = e.val.2.val := congrArg Prod.snd hc
  have hbin : ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ = L.tag e.val.1 0 :=
    congrArg (fun c => c.1 0) hc
  have ht := p.baseGood_domain_bounds hh hg hb hω.2
  change 0 ≤ domainTime h (p.domainCode k h g b ω) ∧
    domainTime h (p.domainCode k h g b ω) ≤ 1 ∧
    |domainVelocity g (p.domainCode k h g b ω)| ≤ p.K k + g at ht
  rw [hdomain] at ht
  have hv := p.baseGood_major_velocity_bound (m := m) hN hω.2
  rw [hbin] at hv
  exact ⟨ht.1, ht.2.1, ht.2.2, hv⟩

end ProjectedLayer
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
