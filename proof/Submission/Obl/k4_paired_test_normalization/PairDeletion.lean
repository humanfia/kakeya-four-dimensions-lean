-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/PairDeletion.lean. Existing attribution comments are retained below.

import Mathlib

namespace Submission.Obl.k4_paired_test_normalization

open Set MeasureTheory

/-- Deleting a bad set in either role costs two marginal budgets. Columns have
no source multiplicity; rows may have many possible witnesses. -/
theorem two_role_deletion_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (H : ι → ι → Set Ω) (Bad : ι → Set Ω) (b : ι → ENNReal)
    (hH : ∀ i j, MeasurableSet (H i j)) (hBad : ∀ i, MeasurableSet (Bad i))
    (hdisj : ∀ j, Pairwise fun i k => Disjoint (H i j) (H k j))
    (hsource : ∀ i, μ ((⋃ j, H i j) ∩ Bad i) ≤ b i)
    (hwitness : ∀ j, μ ((⋃ i, H i j) ∩ Bad j) ≤ b j) :
    (∑ i, μ (⋃ j, H i j)) ≤
      (∑ i, μ (⋃ j, H i j \ (Bad i ∪ Bad j))) + 2 * ∑ i, b i := by
  classical
  have hcover (i) : (⋃ j, H i j) ⊆ (⋃ j, H i j \ (Bad i ∪ Bad j)) ∪
      (((⋃ j, H i j) ∩ Bad i) ∪ (⋃ j, H i j ∩ Bad j)) := by
    intro p hp
    obtain ⟨j, hj⟩ := mem_iUnion.mp hp
    by_cases hi : p ∈ Bad i
    · exact Or.inr (Or.inl ⟨mem_iUnion.mpr ⟨j, hj⟩, hi⟩)
    · by_cases hjbad : p ∈ Bad j
      · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨j, hj, hjbad⟩))
      · exact Or.inl (mem_iUnion.mpr ⟨j, hj, fun h => h.elim hi hjbad⟩)
  have hrow (i) : μ (⋃ j, H i j) ≤ μ (⋃ j, H i j \ (Bad i ∪ Bad j)) +
      μ ((⋃ j, H i j) ∩ Bad i) + μ (⋃ j, H i j ∩ Bad j) := by
    calc
      _ ≤ μ ((⋃ j, H i j \ (Bad i ∪ Bad j)) ∪
          (((⋃ j, H i j) ∩ Bad i) ∪ (⋃ j, H i j ∩ Bad j))) := measure_mono (hcover i)
      _ ≤ μ (⋃ j, H i j \ (Bad i ∪ Bad j)) +
          (μ ((⋃ j, H i j) ∩ Bad i) + μ (⋃ j, H i j ∩ Bad j)) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ = _ := (add_assoc _ _ _).symm
  have hcolumn (j) : μ (⋃ i, H i j ∩ Bad j) = ∑ i, μ (H i j ∩ Bad j) := by
    rw [measure_iUnion (fun i k hik =>
      (hdisj j hik).mono inter_subset_left inter_subset_left)
      (fun i => (hH i j).inter (hBad j)), tsum_fintype]
  have hwit : (∑ i, μ (⋃ j, H i j ∩ Bad j)) ≤ ∑ j, b j := by
    calc
      _ ≤ ∑ i, ∑ j, μ (H i j ∩ Bad j) :=
        Finset.sum_le_sum (fun i _ => measure_iUnion_fintype_le μ _)
      _ = ∑ j, ∑ i, μ (H i j ∩ Bad j) := Finset.sum_comm
      _ = ∑ j, μ ((⋃ i, H i j) ∩ Bad j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [iUnion_inter, hcolumn j]
      _ ≤ ∑ j, b j := Finset.sum_le_sum (fun j _ => hwitness j)
  calc
    _ ≤ ∑ i, (μ (⋃ j, H i j \ (Bad i ∪ Bad j)) +
        μ ((⋃ j, H i j) ∩ Bad i) + μ (⋃ j, H i j ∩ Bad j)) :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = (∑ i, μ (⋃ j, H i j \ (Bad i ∪ Bad j))) +
        (∑ i, μ ((⋃ j, H i j) ∩ Bad i)) + (∑ i, μ (⋃ j, H i j ∩ Bad j)) := by
      simp only [Finset.sum_add_distrib]
    _ ≤ (∑ i, μ (⋃ j, H i j \ (Bad i ∪ Bad j))) + (∑ i, b i) + (∑ i, b i) :=
      add_le_add (add_le_add le_rfl (Finset.sum_le_sum (fun i _ => hsource i))) hwit
    _ = _ := by rw [two_mul, add_assoc]

/-- A uniform count and density budget in each world/block gives a weighted
quadratic budget after summing the original world weights. -/
theorem weighted_fiber_budget {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (lab : ι → κ) (w : κ → ℝ) (β : ι → ℝ) {A σ : ℝ}
    (hA : 0 ≤ A) (hσ : 0 < σ) (hw : ∀ k, 0 ≤ w k)
    (hβ : ∀ i, β i ≤ σ * A)
    (hcard : ∀ k, (((Finset.univ.filter (fun i => lab i = k)).card : ℕ) : ℝ) ≤ A / σ) :
    ∑ i, w (lab i) * β i ≤ A ^ 2 * ∑ k, w k := by
  classical
  have hfiber (k : κ) : (∑ i ∈ Finset.univ.filter (fun i => lab i = k), β i) ≤ A ^ 2 := by
    calc
      _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => lab i = k), σ * A :=
        Finset.sum_le_sum (fun i _ => hβ i)
      _ = ((Finset.univ.filter (fun i => lab i = k)).card : ℝ) * (σ * A) := by simp
      _ ≤ (A / σ) * (σ * A) := mul_le_mul_of_nonneg_right (hcard k) (by positivity)
      _ = A ^ 2 := by field_simp [hσ.ne']
  calc
    _ = ∑ k, ∑ i ∈ Finset.univ.filter (fun i => lab i = k), w (lab i) * β i :=
      (Finset.sum_fiberwise Finset.univ lab (fun i => w (lab i) * β i)).symm
    _ = ∑ k, w k * ∑ i ∈ Finset.univ.filter (fun i => lab i = k), β i := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ ≤ ∑ k, w k * A ^ 2 := Finset.sum_le_sum (fun k _ =>
      mul_le_mul_of_nonneg_left (hfiber k) (hw k))
    _ = A ^ 2 * ∑ k, w k := by rw [← Finset.sum_mul]; ring

end Submission.Obl.k4_paired_test_normalization
