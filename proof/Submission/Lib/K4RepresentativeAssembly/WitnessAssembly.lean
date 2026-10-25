import Submission.Lib.K4RepresentativeAssembly.SourceAssignments
import Submission.Lib.K4RepresentativeAssembly.BinAssembly

/-!
Adapted from: here:o114 (session x0383).

The output incidence events can be assembled from old witness events. Their
format therefore needs no analytic or observation-list membership predicate.
-/

namespace Submission.Lib.K4RepresentativeAssembly

open Set MeasureTheory

/-- Merge the old witness events selected by a fixed finite compatibility table,
then cut by the output label's geometric assignment. -/
def mergedWitnessEvents {Y β : Type*} [DecidableEq β] {m : ℕ}
    (F : Fin m → Set Y) (compat : Fin m → Finset β) (G : β → Set Y) (b : β) : Set Y :=
  (⋃ w, if b ∈ compat w then F w else ∅) ∩ G b

theorem mem_mergedWitnessEvents {Y β : Type*} [DecidableEq β] {m : ℕ}
    (F : Fin m → Set Y) (compat : Fin m → Finset β) (G : β → Set Y) (b : β) (y : Y) :
    y ∈ mergedWitnessEvents F compat G b ↔
      (∃ w, b ∈ compat w ∧ y ∈ F w) ∧ y ∈ G b := by
  simp [mergedWitnessEvents]

theorem witness_mem_mergedWitnessEvents {Y β : Type*} [DecidableEq β] {m : ℕ}
    (F : Fin m → Set Y) (compat : Fin m → Finset β) (G : β → Set Y)
    {w : Fin m} {b : β} {y : Y} (hF : y ∈ F w) (hb : b ∈ compat w) (hG : y ∈ G b) :
    y ∈ mergedWitnessEvents F compat G b :=
  (mem_mergedWitnessEvents F compat G b y).mpr ⟨⟨w, hb, hF⟩, hG⟩

theorem mergedWitnessEvents_subset {Y β : Type*} [DecidableEq β] {m : ℕ}
    (F : Fin m → Set Y) (compat : Fin m → Finset β) (G : β → Set Y)
    (E : Set Y) (hF : ∀ w, F w ⊆ E) (b : β) :
    mergedWitnessEvents F compat G b ⊆ E := by
  intro y hy
  obtain ⟨⟨w, _, hw⟩, _⟩ := (mem_mergedWitnessEvents F compat G b y).mp hy
  exact hF w hw

theorem measurableSet_mergedWitnessEvents {Y β : Type*} [MeasurableSpace Y]
    [DecidableEq β] {m : ℕ} (F : Fin m → Set Y) (compat : Fin m → Finset β)
    (G : β → Set Y) (hF : ∀ w, MeasurableSet (F w))
    (hG : ∀ b, MeasurableSet (G b)) (b : β) :
    MeasurableSet (mergedWitnessEvents F compat G b) := by
  apply MeasurableSet.inter _ (hG b)
  apply MeasurableSet.iUnion
  intro w
  split_ifs
  · exact hF w
  · exact MeasurableSet.empty

/-- Only geometric output assignments need to be disjoint. -/
theorem mergedWitnessEvents_pairwise {Y β : Type*} [DecidableEq β] {m : ℕ}
    (F : Fin m → Set Y) (compat : Fin m → Finset β) (G : β → Set Y)
    (hG : Pairwise (fun b c => Disjoint (G b) (G c))) :
    Pairwise (fun b c => Disjoint (mergedWitnessEvents F compat G b)
      (mergedWitnessEvents F compat G c)) := by
  intro b c hbc
  exact (hG hbc).mono inter_subset_right inter_subset_right

/-- Membership of an old witness event already certifies the new list condition. -/
theorem mergedWitnessEvents_list {Y Ω β : Type*} [DecidableEq β] {m : ℕ}
    (F : Fin m → Set Y) (compat : Fin m → Finset β) (G : β → Set Y)
    (obs : Y → Ω) (oldList : Ω → Finset (Fin m))
    (hF : ∀ w y, y ∈ F w → w ∈ oldList (obs y))
    {b : β} {y : Y} (hy : y ∈ mergedWitnessEvents F compat G b) :
    b ∈ composedList (oldList (obs y)) compat := by
  obtain ⟨⟨w, hb, hw⟩, _⟩ := (mem_mergedWitnessEvents F compat G b y).mp hy
  exact mem_composedList (hF w y hw) hb

/-- Every retained successful witness is covered, with the original law. -/
theorem successfulMass_le_mergedWitnessEvents {Y β : Type*} [MeasurableSpace Y]
    [DecidableEq β] [Fintype β] {m : ℕ} (μ : Measure Y)
    (F : Fin m → Set Y) (compat : Fin m → Finset β) (G : β → Set Y) (S : Set Y)
    (hS : ∀ y ∈ S, ∃ w b, y ∈ F w ∧ b ∈ compat w ∧ y ∈ G b) :
    μ S ≤ ∑ b, μ (mergedWitnessEvents F compat G b) := by
  have hcover : S ⊆ ⋃ b, mergedWitnessEvents F compat G b := by
    intro y hy
    obtain ⟨w,b,hw,hb,hG⟩ := hS y hy
    exact mem_iUnion.mpr ⟨b, witness_mem_mergedWitnessEvents F compat G hw hb hG⟩
  exact (measure_mono hcover).trans (measure_iUnion_fintype_le μ _)

/-- Finite-format old witness events and a geometric cut give finite-format
output events; the compatibility table contributes no polynomial atoms. -/
theorem fmt_mergedWitnessEvents {β : Type*} [DecidableEq β] {n m D D' : ℕ}
    {H H' : ℝ} (F : Fin m → Set (Fin n → ℝ)) (compat : Fin m → Finset β)
    (G : β → Set (Fin n → ℝ)) (hH : 0 ≤ H)
    (hF : ∀ w, fmt n H D (F w)) (hG : ∀ b, fmt n H' D' (G b)) (b : β) :
    fmt n ((m : ℝ)*H + H') (max D D') (mergedWitnessEvents F compat G b) := by
  have hunion : fmt n ((m : ℝ)*H) D (⋃ w, if b ∈ compat w then F w else ∅) := by
    simpa only [decide_eq_true_eq] using
      fmt_selected_iUnion F (fun w => decide (b ∈ compat w)) true hH hF
  exact fmt_inter hunion (hG b)

/-- The old list fibers already provide measurability of composed lists. -/
theorem measurableSet_composedList_membership {Y β : Type*} [MeasurableSpace Y]
    [DecidableEq β] {m : ℕ} (oldList : Y → Finset (Fin m))
    (compat : Fin m → Finset β) (hOld : ∀ w, MeasurableSet {y | w ∈ oldList y}) (b : β) :
    MeasurableSet {y | b ∈ composedList (oldList y) compat} := by
  have heq : {y | b ∈ composedList (oldList y) compat} =
      mergedWitnessEvents (fun w => {y | w ∈ oldList y}) compat (fun _ => univ) b := by
    ext y
    simp [composedList, mergedWitnessEvents, and_comm]
  rw [heq]
  exact measurableSet_mergedWitnessEvents _ compat _ hOld (fun _ => MeasurableSet.univ) b

/-- The paired interface's format for each old list fiber is sufficient for
fixed format of every composed-list fiber. -/
theorem fmt_composedList_membership {β : Type*} [DecidableEq β] {n m D : ℕ}
    {H : ℝ} (oldList : (Fin n → ℝ) → Finset (Fin m)) (compat : Fin m → Finset β)
    (hH : 0 ≤ H) (hOld : ∀ w, fmt n H D {y | w ∈ oldList y}) (b : β) :
    fmt n ((m : ℝ)*H) D {y | b ∈ composedList (oldList y) compat} := by
  have heq : {y | b ∈ composedList (oldList y) compat} =
      ⋃ w, if b ∈ compat w then {y | w ∈ oldList y} else ∅ := by
    ext y
    simp [composedList, and_comm]
  rw [heq]
  simpa only [decide_eq_true_eq] using
    fmt_selected_iUnion (fun w => {y | w ∈ oldList y})
      (fun w => decide (b ∈ compat w)) true hH hOld

end Submission.Lib.K4RepresentativeAssembly
