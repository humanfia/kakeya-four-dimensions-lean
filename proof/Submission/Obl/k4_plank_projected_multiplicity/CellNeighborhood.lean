import Submission.Obl.k4_plank_projected_multiplicity.Multiplicity

namespace Submission.Obl.k4_plank_projected_multiplicity

open Finset

noncomputable section

def heavyLabels {α β : Type*} [DecidableEq β] (T : Finset α) (f : α → β) (M : ℝ) :
    Finset β := by
  classical
  exact (T.image f).filter (fun q => M ≤ ((T.filter (fun p => f p = q)).card : ℝ))

/-- Enlarging the occupied heavy cells by a bounded number of neighbors costs only
that bounded factor in incidence count, even if the neighboring cells are light. -/
theorem card_pairs_near_heavy_labels {α β : Type*} [DecidableEq β]
    (T : Finset α) (f : α → β) {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (E : Finset β) (hE : (E.card : ℝ) ≤ K * ((heavyLabels T f M).card : ℝ)) :
    ((T.filter (fun p => f p ∈ E)).card : ℝ) ≤
      (K + 1) * ((T.filter (fun p => f p ∈ heavyLabels T f M)).card : ℝ) := by
  classical
  let H := heavyLabels T f M
  let count : β → ℝ := fun q => ((T.filter (fun p => f p = q)).card : ℝ)
  have hsum (U : Finset β) : (∑ q ∈ U, count q) =
      ((T.filter (fun p => f p ∈ U)).card : ℝ) := by
    simpa [count] using Finset.sum_fiberwise_eq_sum_filter T U f (fun _ => (1 : ℝ))
  have hmin : M * (H.card : ℝ) ≤ ((T.filter (fun p => f p ∈ H)).card : ℝ) := by
    calc
      M * (H.card : ℝ) = ∑ _q ∈ H, M := by simp [mul_comm]
      _ ≤ ∑ q ∈ H, count q :=
        Finset.sum_le_sum (fun q hq => (Finset.mem_filter.mp hq).2)
      _ = _ := hsum H
  have hlight (q : β) (hq : q ∉ H) : count q ≤ M := by
    by_cases hqT : q ∈ T.image f
    · have hn : ¬M ≤ count q := fun h => hq (Finset.mem_filter.mpr ⟨hqT, h⟩)
      exact (lt_of_not_ge hn).le
    · have he : T.filter (fun p => f p = q) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro p hp heq
        exact hqT (Finset.mem_image.mpr ⟨p, hp, heq⟩)
      simpa only [count, he, Finset.card_empty, Nat.cast_zero] using hM
  have hsmall : (E.card : ℝ) * M ≤
      K * ((T.filter (fun p => f p ∈ H)).card : ℝ) := by
    calc
      (E.card : ℝ) * M ≤ (K * (H.card : ℝ)) * M := mul_le_mul_of_nonneg_right hE hM
      _ = K * (M * (H.card : ℝ)) := by ring
      _ ≤ K * ((T.filter (fun p => f p ∈ H)).card : ℝ) :=
        mul_le_mul_of_nonneg_left hmin hK
  calc
    ((T.filter (fun p => f p ∈ E)).card : ℝ) = ∑ q ∈ E, count q := (hsum E).symm
    _ ≤ ∑ q ∈ E, ((if q ∈ H then count q else 0) + M) := by
      apply Finset.sum_le_sum
      intro q hq
      by_cases hqh : q ∈ H
      · simp only [hqh, ↓reduceIte]
        linarith
      · simpa only [hqh, ↓reduceIte, zero_add] using hlight q hqh
    _ = (∑ q ∈ E.filter (fun q => q ∈ H), count q) + (E.card : ℝ) * M := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp
    _ ≤ (∑ q ∈ H, count q) + (E.card : ℝ) * M := by
      apply add_le_add_left
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact fun q hq => (Finset.mem_filter.mp hq).2
      · intro q hq hq'
        exact Nat.cast_nonneg _
    _ = ((T.filter (fun p => f p ∈ H)).card : ℝ) + (E.card : ℝ) * M := by rw [hsum H]
    _ ≤ ((T.filter (fun p => f p ∈ H)).card : ℝ) +
        K * ((T.filter (fun p => f p ∈ H)).card : ℝ) := add_le_add_right hsmall _
    _ = (K + 1) * ((T.filter (fun p => f p ∈ H)).card : ℝ) := by ring

def expandProjectedCells (H : Finset (ℕ × (Fin 2 → ℤ))) (Ω : Finset (Fin 2 → ℤ)) :
    Finset (ℕ × (Fin 2 → ℤ)) :=
  (H.product Ω).image (fun p => (p.1.1, fun j => p.1.2 j + p.2 j))

theorem card_expandProjectedCells (H : Finset (ℕ × (Fin 2 → ℤ)))
    (Ω : Finset (Fin 2 → ℤ)) :
    (expandProjectedCells H Ω).card ≤ H.card * Ω.card := by
  apply (Finset.card_image_le).trans
  change (H ×ˢ Ω).card ≤ H.card * Ω.card
  rw [Finset.card_product]

theorem heavy_pairs_eq_sigma_marks {ι κ β : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq β] (f : (Σ _ : ι, κ) → β) (M : ℝ) :
    (((univ : Finset ι).sigma (fun _ => (univ : Finset κ))).filter
      (fun p => f p ∈ heavyLabels (univ.sigma (fun _ => univ)) f M)) =
        univ.sigma (highCellMarks f M) := by
  classical
  ext p
  simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and,
    heavyLabels, highCellMarks]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Finset.mem_image.mpr ⟨p, by simp, rfl⟩, h⟩

theorem card_pairs_in_expanded_heavy_cells {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : (Σ _ : ι, κ) → ℕ × (Fin 2 → ℤ)) {M : ℝ} (hM : 0 ≤ M)
    (Ω : Finset (Fin 2 → ℤ)) :
    ((((univ : Finset ι).sigma (fun _ => (univ : Finset κ))).filter
      (fun p => f p ∈ expandProjectedCells
        (heavyLabels (univ.sigma (fun _ => univ)) f M) Ω)).card : ℝ) ≤
      ((Ω.card : ℝ) + 1) * ∑ i : ι, ((highCellMarks f M i).card : ℝ) := by
  have hE : ((expandProjectedCells (heavyLabels (univ.sigma (fun _ => univ)) f M) Ω).card : ℝ) ≤
      (Ω.card : ℝ) * ((heavyLabels (univ.sigma (fun _ => univ)) f M).card : ℝ) := by
    have h := card_expandProjectedCells (heavyLabels (univ.sigma (fun _ => univ)) f M) Ω
    exact_mod_cast h.trans_eq (Nat.mul_comm _ _)
  have h := card_pairs_near_heavy_labels (univ.sigma (fun _ => univ)) f hM
    (Nat.cast_nonneg Ω.card) _ hE
  rw [heavy_pairs_eq_sigma_marks] at h
  simpa only [Finset.card_sigma, Nat.cast_sum] using h

end

end Submission.Obl.k4_plank_projected_multiplicity
