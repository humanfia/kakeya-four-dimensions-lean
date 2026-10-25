import Submission.Obl.k4_scalar_grid_density_extension.GridRelation

noncomputable section

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MeasureTheory Set
open scoped ENNReal

/-- The list available from a finer bin is the union of the two possible old
coarse-bin lists. Real-power grids need not be nested. -/
def coarsenList {Z I : Type*} [DecidableEq I] (Λ : Z × ℤ → Finset I)
    (w w' : ℝ) (p : Z × ℤ) : Finset I :=
  Λ (p.1, ⌊(p.2 : ℝ) * w' / w⌋) ∪ Λ (p.1, ⌊(p.2 : ℝ) * w' / w⌋ + 1)

theorem measurableSet_mem_coarsenList {Z I : Type*} [MeasurableSpace Z] [DecidableEq I]
    (Λ : Z × ℤ → Finset I) (hΛ : ∀ i, MeasurableSet {p | i ∈ Λ p})
    (w w' : ℝ) (i : I) : MeasurableSet {p | i ∈ coarsenList Λ w w' p} := by
  have hm (e : ℤ) : Measurable (fun p : Z × ℤ =>
      (p.1, ⌊(p.2 : ℝ) * w' / w⌋ + e)) :=
    measurable_fst.prodMk ((measurable_of_countable
      (fun k : ℤ => ⌊(k : ℝ) * w' / w⌋ + e)).comp measurable_snd)
  have h0 := (hΛ i).preimage (hm 0)
  have h1 := (hΛ i).preimage (hm 1)
  convert h0.union h1 using 1
  ext p
  simp [coarsenList]

theorem card_coarsenList_le {Z I : Type*} [DecidableEq I]
    (Λ : Z × ℤ → Finset I) (w w' : ℝ) (D : ℝ≥0∞)
    (hD : ∀ p, ((Λ p).card : ℝ≥0∞) ≤ D) (p : Z × ℤ) :
    ((coarsenList Λ w w' p).card : ℝ≥0∞) ≤ 2 * D := by
  calc
    _ ≤ ((Λ (p.1, ⌊(p.2 : ℝ) * w' / w⌋)).card : ℝ≥0∞) +
        ((Λ (p.1, ⌊(p.2 : ℝ) * w' / w⌋ + 1)).card : ℝ≥0∞) := by
      exact_mod_cast Finset.card_union_le (Λ (p.1, ⌊(p.2 : ℝ) * w' / w⌋))
        (Λ (p.1, ⌊(p.2 : ℝ) * w' / w⌋ + 1))
    _ ≤ D + D := add_le_add (hD _) (hD _)
    _ = 2 * D := (two_mul D).symm

theorem mem_coarsenList_of_mem {Z I : Type*} [DecidableEq I]
    (Λ : Z × ℤ → Finset I) {w w' : ℝ} (hw' : 0 < w') (hww' : w' ≤ w)
    {z : Z} {x : ℝ} {i : I} (hi : i ∈ Λ (z, ⌊x / w⌋)) :
    i ∈ coarsenList Λ w w' (z, ⌊x / w'⌋) := by
  have h := k4_scalar_grid_density_extension.floorCompatible_coarse_mem hw' hww'
    ⌊x / w'⌋ ⌊x / w⌋ ⟨x, rfl, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · exact Finset.mem_union.mpr (Or.inl (by simpa only [← h] using hi))
  · exact Finset.mem_union.mpr (Or.inr (by simpa only [← h] using hi))

end Submission.Obl.k4_scalar_true_terminal_lifting
