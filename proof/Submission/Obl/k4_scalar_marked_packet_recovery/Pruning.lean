import Submission.Obl.k4_scalar_marked_packet_recovery.Definitions

namespace Submission.Obl.k4_scalar_marked_packet_recovery

open Set MeasureTheory
open scoped ENNReal

/-- Discard packets below their required floor and enumerate the retained labels. -/
theorem prune_finite_sets {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {n : ℕ} (C : Fin n → Set X) (hC : ∀ i, MeasurableSet (C i))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    {r f : ℝ≥0∞} (hr : r ≠ ∞) (htotal : r + r ≤ μ (⋃ i, C i))
    (hbudget : (n : ℝ≥0∞) * f ≤ r) :
    ∃ (n' : ℕ) (e : Fin n' → Fin n), Function.Injective e ∧
      (∀ i, f ≤ μ (C (e i))) ∧ r ≤ μ (⋃ i, C (e i)) := by
  classical
  let good : Finset (Fin n) := Finset.univ.filter (fun i => f ≤ μ (C i))
  let bad : Finset (Fin n) := Finset.univ.filter (fun i => ¬f ≤ μ (C i))
  have hbad : ∑ i ∈ bad, μ (C i) ≤ r := by
    calc
      _ ≤ ∑ i ∈ bad, f := by
        apply Finset.sum_le_sum
        intro i hi
        exact (lt_of_not_ge (Finset.mem_filter.mp hi).2).le
      _ ≤ ∑ i : Fin n, f := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (by intros; exact zero_le)
      _ = (n : ℝ≥0∞) * f := by simp
      _ ≤ r := hbudget
  have hsum : (∑ i ∈ good, μ (C i)) + ∑ i ∈ bad, μ (C i) = ∑ i, μ (C i) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hgood : r ≤ ∑ i ∈ good, μ (C i) := by
    apply ENNReal.le_of_add_le_add_right hr
    calc
      r + r ≤ μ (⋃ i, C i) := htotal
      _ = ∑ i, μ (C i) := by rw [measure_iUnion hdisj hC, tsum_fintype]
      _ = (∑ i ∈ good, μ (C i)) + ∑ i ∈ bad, μ (C i) := hsum.symm
      _ ≤ (∑ i ∈ good, μ (C i)) + r := by gcongr
  let T := {i : Fin n // i ∈ good}
  let e : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  refine ⟨Fintype.card T, fun i => (e i).val, ?_, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro i
    exact (Finset.mem_filter.mp (e i).property).2
  · rw [measure_iUnion, tsum_fintype]
    · calc
        r ≤ ∑ i ∈ good, μ (C i) := hgood
        _ = ∑ i : T, μ (C i.val) := Finset.sum_subtype good (by simp) _
        _ = ∑ i, μ (C (e i).val) := (e.sum_comp _).symm
    · intro i j hij
      exact hdisj (by intro h; exact hij (e.injective (Subtype.ext h)))
    · intro i
      exact hC _

/-- A disjoint family of noisy packets cannot spend more than the law's total mass. -/
theorem packet_floor_budget {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {n : ℕ} (C : Fin n → Set X) (hC : ∀ i, MeasurableSet (C i))
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    {f : ℝ≥0∞} (hfloor : ∀ i, f ≤ μ (C i)) (hmass : μ univ ≤ 1) :
    (n : ℝ≥0∞) * f ≤ 1 := by
  calc
    _ = ∑ i : Fin n, f := by simp
    _ ≤ ∑ i, μ (C i) := Finset.sum_le_sum (fun i _ => hfloor i)
    _ = μ (⋃ i, C i) := by rw [measure_iUnion hdisj hC, tsum_fintype]
    _ ≤ μ univ := measure_mono (subset_univ _)
    _ ≤ 1 := hmass

end Submission.Obl.k4_scalar_marked_packet_recovery
