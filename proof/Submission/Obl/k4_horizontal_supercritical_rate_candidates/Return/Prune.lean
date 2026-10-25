import Mathlib

/-!
# Summable reference-weight pruning

Entries `e` carry sets `E e` and reference weights `R e`. Deleting the entries whose
current mass is below `R e / K₁` loses at most `(∑' e, R e) / K₁`. This is the pruning
step of the supplied paper (Remark `a06:summable-pruning`), in the form used repeatedly by
the supercritical return.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory
open scoped ENNReal

/-- The union of light entries. -/
def lightUnion {X ι : Type*} [MeasurableSpace X] (m : Measure X) (E : ι → Set X) (R : ι → ℝ≥0∞) (K₁ : ℝ≥0∞) :
    Set X :=
  ⋃ e ∈ {e | m (E e) < R e / K₁}, E e

theorem measure_lightUnion_le {X ι : Type*} [MeasurableSpace X] [Countable ι] (m : Measure X)
    (E : ι → Set X) (R : ι → ℝ≥0∞) (K₁ : ℝ≥0∞) :
    m (lightUnion m E R K₁) ≤ (∑' e, R e) / K₁ := by
  unfold lightUnion
  calc m (⋃ e ∈ {e | m (E e) < R e / K₁}, E e)
      ≤ ∑' e : {e | m (E e) < R e / K₁}, m (E e) := measure_biUnion_le _ (Set.to_countable _) _
    _ ≤ ∑' e : {e | m (E e) < R e / K₁}, R e / K₁ :=
        ENNReal.tsum_le_tsum (fun e => e.2.le)
    _ ≤ ∑' e, R e / K₁ :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun e => R e / K₁)
    _ = (∑' e, R e) / K₁ := by
        simp only [div_eq_mul_inv]
        exact ENNReal.tsum_mul_right

/-- A point lying in a non-light entry: its entry's mass is at least the scaled reference. -/
theorem heavy_of_not_mem_lightUnion {X ι : Type*} [MeasurableSpace X] {m : Measure X} {E : ι → Set X}
    {R : ι → ℝ≥0∞} {K₁ : ℝ≥0∞} {x : X} {e : ι} (hx : x ∈ E e)
    (hnot : x ∉ lightUnion m E R K₁) : R e / K₁ ≤ m (E e) := by
  by_contra hlt
  push Not at hlt
  exact hnot (Set.mem_biUnion (show e ∈ {e | m (E e) < R e / K₁} from hlt) hx)

theorem measurableSet_lightUnion {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (m : Measure X) (E : ι → Set X) (R : ι → ℝ≥0∞) (K₁ : ℝ≥0∞)
    (hE : ∀ e, MeasurableSet (E e)) : MeasurableSet (lightUnion m E R K₁) := by
  unfold lightUnion
  exact MeasurableSet.biUnion (Set.to_countable _) (fun e _ => hE e)

/-- One pruning step: delete light entries and null entries. -/
def pruned {X ι : Type*} [MeasurableSpace X] (m : Measure X) (G : Set X) (E : ι → Set X)
    (R : ι → ℝ≥0∞) (K₁ : ℝ≥0∞) : Set X :=
  G \ (lightUnion m E R K₁ ∪ ⋃ e ∈ {e | m (E e) = 0}, E e)

theorem pruned_subset {X ι : Type*} [MeasurableSpace X] (m : Measure X) (G : Set X)
    (E : ι → Set X) (R : ι → ℝ≥0∞) (K₁ : ℝ≥0∞) : pruned m G E R K₁ ⊆ G :=
  Set.diff_subset

theorem measurableSet_pruned {X ι : Type*} [MeasurableSpace X] [Countable ι] (m : Measure X)
    {G : Set X} (hG : MeasurableSet G) (E : ι → Set X) (R : ι → ℝ≥0∞) (K₁ : ℝ≥0∞)
    (hE : ∀ e, MeasurableSet (E e)) : MeasurableSet (pruned m G E R K₁) := by
  unfold pruned
  exact hG.diff ((measurableSet_lightUnion m E R K₁ hE).union
    (MeasurableSet.biUnion (Set.to_countable _) (fun e _ => hE e)))

/-- The loss of one pruning step. -/
theorem measure_diff_pruned_le {X ι : Type*} [MeasurableSpace X] [Countable ι] (m : Measure X)
    (G : Set X) (E : ι → Set X) (R : ι → ℝ≥0∞) (K₁ : ℝ≥0∞) :
    m (G \ pruned m G E R K₁) ≤ (∑' e, R e) / K₁ := by
  have hnull : m (⋃ e ∈ {e | m (E e) = 0}, E e) = 0 :=
    measure_biUnion_null_iff (Set.to_countable _) |>.mpr (fun e he => he)
  have hsub : G \ pruned m G E R K₁ ⊆ lightUnion m E R K₁ ∪ ⋃ e ∈ {e | m (E e) = 0}, E e := by
    intro x hx
    by_contra hc
    exact hx.2 ⟨hx.1, hc⟩
  calc m (G \ pruned m G E R K₁)
      ≤ m (lightUnion m E R K₁ ∪ ⋃ e ∈ {e | m (E e) = 0}, E e) := measure_mono hsub
    _ ≤ m (lightUnion m E R K₁) + m (⋃ e ∈ {e | m (E e) = 0}, E e) := measure_union_le _ _
    _ = m (lightUnion m E R K₁) := by rw [hnull, add_zero]
    _ ≤ _ := measure_lightUnion_le m E R K₁

/-- Points surviving a pruning step see their entries heavy and non-null. -/
theorem heavy_of_mem_pruned {X ι : Type*} [MeasurableSpace X] {m : Measure X} {G : Set X}
    {E : ι → Set X} {R : ι → ℝ≥0∞} {K₁ : ℝ≥0∞} {x : X} (hx : x ∈ pruned m G E R K₁)
    {e : ι} (hxe : x ∈ E e) : R e / K₁ ≤ m (E e) ∧ m (E e) ≠ 0 := by
  have hx2 := hx.2
  refine ⟨heavy_of_not_mem_lightUnion hxe (fun h => hx2 (Or.inl h)), ?_⟩
  intro h0
  exact hx2 (Or.inr (Set.mem_biUnion (show e ∈ {e | m (E e) = 0} from h0) hxe))

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
