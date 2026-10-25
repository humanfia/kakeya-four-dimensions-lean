import Mathlib

namespace Submission.Obl.k4_plank_projected_multiplicity

open Finset

/-- A lower bound for every occupied fiber controls the number of occupied labels. -/
theorem image_mul_min_fiber_le_card {α β : Type*} [DecidableEq β]
    (S : Finset α) (f : α → β) (M : ℝ)
    (hM : ∀ q ∈ S.image f, M ≤ ((S.filter (fun i => f i = q)).card : ℝ)) :
    M * ((S.image f).card : ℝ) ≤ (S.card : ℝ) := by
  classical
  have hsum := Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image f)
    (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩) (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  calc
    M * ((S.image f).card : ℝ) = ∑ _q ∈ S.image f, M := by simp [mul_comm]
    _ ≤ ∑ q ∈ S.image f, ((S.filter (fun i => f i = q)).card : ℝ) :=
      Finset.sum_le_sum hM
    _ = (S.card : ℝ) := hsum

/-- Pruning short traces converts a dense-row incidence estimate to a tail estimate.

The input `hrows` is the conclusion of the plank estimate after restricting to the
long traces. Every occupied label has multiplicity at least `M`; if `M ≥ 2 * B`,
at most `2 * #ι * d` marked incidences remain.
-/
theorem incidence_pruning_of_support {ι κ β : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq β] (J : ι → Finset κ) (f : (Σ _ : ι, κ) → β)
    {d B M : ℝ} (hd : 0 ≤ d) (hB : 0 ≤ B) (hM : 2 * B ≤ M)
    (hsupport : M * ((((univ : Finset ι).sigma J).image f).card : ℝ) ≤
      ∑ i : ι, ((J i).card : ℝ))
    (hrows : ∀ S : Finset ι, (∀ i ∈ S, d ≤ ((J i).card : ℝ)) →
      (∑ i ∈ S, ((J i).card : ℝ)) ≤ B * (((S.sigma J).image f).card : ℝ)) :
    (∑ i : ι, ((J i).card : ℝ)) ≤ 2 * (Fintype.card ι : ℝ) * d := by
  classical
  let L : Finset ι := univ.filter (fun i => d ≤ ((J i).card : ℝ))
  let S : Finset ι := univ.filter (fun i => ¬d ≤ ((J i).card : ℝ))
  have hlong : (∑ i ∈ L, ((J i).card : ℝ)) ≤
      B * (((univ.sigma J).image f).card : ℝ) := by
    calc
      (∑ i ∈ L, ((J i).card : ℝ)) ≤ B * (((L.sigma J).image f).card : ℝ) :=
        hrows L (fun i hi => (Finset.mem_filter.mp hi).2)
      _ ≤ B * (((univ.sigma J).image f).card : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hB
        exact_mod_cast Finset.card_le_card (Finset.image_subset_image
          (Finset.sigma_mono (Finset.subset_univ L) (fun _ => Subset.rfl)))
  have hshort : (∑ i ∈ S, ((J i).card : ℝ)) ≤ (Fintype.card ι : ℝ) * d := by
    calc
      (∑ i ∈ S, ((J i).card : ℝ)) ≤ ∑ _i ∈ S, d := by
        apply Finset.sum_le_sum
        intro i hi
        exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hi).2)
      _ = (S.card : ℝ) * d := by simp
      _ ≤ (Fintype.card ι : ℝ) * d :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ S) hd
  have hpartition : (∑ i ∈ L, ((J i).card : ℝ)) + (∑ i ∈ S, ((J i).card : ℝ)) =
      ∑ i : ι, ((J i).card : ℝ) := by
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hm : 2 * B * (((univ.sigma J).image f).card : ℝ) ≤
      M * (((univ.sigma J).image f).card : ℝ) :=
    mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg _)
  nlinarith [hsupport]

/-- The fiberwise form of the pruning estimate. -/
theorem high_multiplicity_pruning {ι κ β : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq β] (J : ι → Finset κ) (f : (Σ _ : ι, κ) → β)
    {d B M : ℝ} (hd : 0 ≤ d) (hB : 0 ≤ B) (hM : 2 * B ≤ M)
    (hfiber : ∀ q ∈ ((univ : Finset ι).sigma J).image f,
      M ≤ ((((univ : Finset ι).sigma J).filter (fun p => f p = q)).card : ℝ))
    (hrows : ∀ S : Finset ι, (∀ i ∈ S, d ≤ ((J i).card : ℝ)) →
      (∑ i ∈ S, ((J i).card : ℝ)) ≤ B * (((S.sigma J).image f).card : ℝ)) :
    (∑ i : ι, ((J i).card : ℝ)) ≤ 2 * (Fintype.card ι : ℝ) * d := by
  apply incidence_pruning_of_support J f hd hB hM _ hrows
  convert image_mul_min_fiber_le_card (univ.sigma J) f M hfiber using 1
  simp [Finset.card_sigma]

noncomputable section

def highCellMarks {ι κ β : Type*} [Fintype ι] [Fintype κ] [DecidableEq β]
    (f : (Σ _ : ι, κ) → β) (M : ℝ) (i : ι) : Finset κ := by
  classical
  exact univ.filter (fun j => M ≤
    ((((univ : Finset ι).sigma (fun _ => (univ : Finset κ))).filter
      (fun p => f p = f ⟨i, j⟩)).card : ℝ))

theorem highCellMarks_fiber {ι κ β : Type*} [Fintype ι] [Fintype κ] [DecidableEq β]
    (f : (Σ _ : ι, κ) → β) (M : ℝ) :
    ∀ q ∈ ((univ : Finset ι).sigma (highCellMarks f M)).image f,
      M ≤ ((((univ : Finset ι).sigma (highCellMarks f M)).filter
        (fun p => f p = q)).card : ℝ) := by
  classical
  intro q hq
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hq
  have hM : M ≤ ((((univ : Finset ι).sigma (fun _ => (univ : Finset κ))).filter
      (fun p => f p = f ⟨i, j⟩)).card : ℝ) :=
    (Finset.mem_filter.mp (Finset.mem_sigma.mp hij).2).2
  have heq : (((univ : Finset ι).sigma (highCellMarks f M)).filter
      (fun p => f p = f ⟨i, j⟩)) =
      (((univ : Finset ι).sigma (fun _ => (univ : Finset κ))).filter
        (fun p => f p = f ⟨i, j⟩)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro hp
      refine ⟨?_, hp⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [hp] using hM
  rw [heq]
  exact hM

end

end Submission.Obl.k4_plank_projected_multiplicity
