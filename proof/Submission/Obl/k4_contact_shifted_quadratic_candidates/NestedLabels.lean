import Submission.Obl.k4_scalar_pair_atlas_assembly.Dyadic
import Submission.Obl.k4_quadratic_finite_greedy_cover.Terminal

/-!
The raw ancestor-identification argument was suggested by this LOT tree,
obligation o223, session x0775, commit a7a28ad1, file
Submission/Obl/k4_contact_parent_horizontal_reduction/NestedTime.lean
(read at branch x0775, commit 245500ae33c3ddf296a9b9b4848622a9fa50270e).
Here it is expressed independently of the ancestor's Data structure and uses
accepted half-open packet disjointness instead of copying its interval proof.
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates

open Set MeasureTheory
open scoped ENNReal

noncomputable section

def closedTimeBlock (T : ℕ) (j : Fin (2 ^ T)) : Set ℝ :=
  Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)

/-- A fixed time is null before and after every incidence restriction. -/
theorem ae_time_ne_of_product_domination {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (C : ℝ≥0∞)
    (hdom : μ ≤ C • ν.prod volume) (t : ℝ) : ∀ᵐ p ∂μ, p.2 ≠ t := by
  apply ae_mono hdom
  apply Measure.ae_smul_measure
  rw [ae_iff]
  simpa only [not_not] using
    Submission.Obl.k4_scalar_pair_atlas_assembly.time_singleton_null ν t

/-- Original assignment/time nesting identifies the prescribed shallow B
label almost everywhere, although the B sets themselves are not nested. -/
theorem ae_deep_in_prescribed_parent
    {α ι κ : Type*} [MeasurableSpace α] [Fintype ι]
    (ν : Measure α) (μ : Measure (α × ℝ)) (C : ℝ≥0∞)
    (hdom : μ ≤ C • ν.prod volume) (T T' : ℕ)
    (j : ι → Fin (2 ^ T)) (j' : κ → Fin (2 ^ T'))
    (A B : ι → Set α) (A' B' : κ → Set α)
    (hBA : ∀ i, B i ⊆ A i) (hBA' : ∀ i, B' i ⊆ A' i)
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i'))
    (hcover : ∀ᵐ p ∂μ, ∃ i, p ∈ B i ×ˢ closedTimeBlock T (j i))
    (parent : κ → ι) (hA : ∀ i, A' i ⊆ A (parent i))
    (hI : ∀ i, closedTimeBlock T' (j' i) ⊆ closedTimeBlock T (j (parent i))) :
    ∀ᵐ p ∂μ, ∀ i, p ∈ B' i ×ˢ closedTimeBlock T' (j' i) →
      p ∈ B (parent i) ×ˢ closedTimeBlock T (j (parent i)) := by
  have htimes : ∀ᵐ p ∂μ, ∀ i : ι,
      p.2 ≠ (((j i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T :=
    ae_all_iff.mpr (fun i => ae_time_ne_of_product_domination ν μ C hdom _)
  have hd := Submission.Obl.k4_quadratic_finite_greedy_cover.halfOpen_packets_disjoint
    A (fun i => (j i : ℕ)) ((2 : ℝ) ^ T) (by positivity)
    (fun i i' hne heq => hdisj i i' hne (Fin.ext heq))
  filter_upwards [hcover, htimes] with p hp ht
  intro i hi
  obtain ⟨a, ha⟩ := hp
  have hparent : parent i = a := by
    by_contra hne
    have hdis := Set.disjoint_left.mp (hd hne)
    apply hdis (a := p)
    · have hpt := hI i hi.2
      exact ⟨hA i (hBA' i hi.1), hpt.1, lt_of_le_of_ne hpt.2 (ht (parent i))⟩
    · exact ⟨hBA a ha.1, ha.2.1, lt_of_le_of_ne ha.2.2 (ht a)⟩
  simpa only [hparent] using ha

/-- The same prescribed-ancestor coverage holds for the actual current law. -/
theorem ae_deep_in_prescribed_parent_of_le
    {α ι κ : Type*} [MeasurableSpace α] [Fintype ι]
    (ν : Measure α) (μ ρ : Measure (α × ℝ)) (C : ℝ≥0∞)
    (hdom : μ ≤ C • ν.prod volume) (hρ : ρ ≤ μ) (T T' : ℕ)
    (j : ι → Fin (2 ^ T)) (j' : κ → Fin (2 ^ T'))
    (A B : ι → Set α) (A' B' : κ → Set α)
    (hBA : ∀ i, B i ⊆ A i) (hBA' : ∀ i, B' i ⊆ A' i)
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i'))
    (hcover : ∀ᵐ p ∂μ, ∃ i, p ∈ B i ×ˢ closedTimeBlock T (j i))
    (parent : κ → ι) (hA : ∀ i, A' i ⊆ A (parent i))
    (hI : ∀ i, closedTimeBlock T' (j' i) ⊆ closedTimeBlock T (j (parent i))) :
    ∀ᵐ p ∂ρ, ∀ i, p ∈ B' i ×ˢ closedTimeBlock T' (j' i) →
      p ∈ B (parent i) ×ˢ closedTimeBlock T (j (parent i)) :=
  ae_mono hρ (ae_deep_in_prescribed_parent ν μ C hdom T T' j j' A B A' B'
    hBA hBA' hdisj hcover parent hA hI)

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates
