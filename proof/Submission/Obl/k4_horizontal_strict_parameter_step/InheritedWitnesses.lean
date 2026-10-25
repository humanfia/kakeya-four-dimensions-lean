/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/InheritedWitnesses.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.Interface
import Submission.Obl.k4_scalar_angular_pair_agreement.Dyadic

/-!
Adapted from this LOT tree, obligation o202, session x0698, branch tip
`a0a908981737978b753644caa836ead37ec79522`, file
`Submission/Obl/k4_horizontal_subcritical_rate_candidates/AncestorWitness.lean`.
The original attribution follows. Its time blocks are definitionally the same as `Iv`.

Unrestricted true-label witnesses are inherited by their assigned ancestor.
The observation is from session x0703's message of 2026-10-21 10:03Z;
this proof uses the frozen model's single affine entry per true label.
-/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

/-- Under prior-times-time domination, a time belongs to only one dyadic
block of a fixed depth almost everywhere, including for closed blocks. -/
lemma ae_unique_dyadic_block {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (C : ENNReal)
    (hμ : μ ≤ C • (ν.prod volume)) (T : ℕ) :
    ∀ᵐ p ∂μ, ∀ j j' : Fin (2 ^ T), p.2 ∈ Iv T j → p.2 ∈ Iv T j' → j = j' := by
  rw [ae_all_iff]
  intro j
  rw [ae_all_iff]
  intro j'
  by_cases h : j = j'
  · exact Filter.Eventually.of_forall (by simp [h])
  · have hnull : μ (univ ×ˢ (Iv T j ∩ Iv T j')) = 0 := by
      apply le_antisymm _ bot_le
      calc μ (univ ×ˢ (Iv T j ∩ Iv T j'))
          ≤ (C • (ν.prod volume)) (univ ×ˢ (Iv T j ∩ Iv T j')) := hμ _
        _ = 0 := by
          have hvol : volume (Iv T j ∩ Iv T j') = 0 :=
            Submission.Obl.k4_scalar_angular_pair_agreement.volume_I_inter T h
          rw [Measure.smul_apply, Measure.prod_prod, hvol]
          simp
    have hevent : ∀ᵐ p ∂μ, p ∉ univ ×ˢ (Iv T j ∩ Iv T j') := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_mem_eq] using hnull
    filter_upwards [hevent] with p hp hpj hpj'
    exact (hp ⟨mem_univ _, hpj, hpj'⟩).elim

/-- The original incidence law already pairs a nested child with its
assigned ancestor's fit set, with no deletion or loss of witness mass. -/
lemma ae_child_mem_ancestor {α ι : Type*} [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (C : ENNReal)
    (hμ : μ ≤ C • (ν.prod volume)) (T : ℕ)
    (j : ι → Fin (2 ^ T)) (A B : ι → Set α)
    (hBA : ∀ i, B i ⊆ A i)
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i'))
    (hcover : ∀ᵐ p ∂μ, ∃ i, p.1 ∈ B i ∧ p.2 ∈ Iv T (j i))
    (h : ι) (Bchild : Set α) (Ichild : Set ℝ)
    (hsub : Bchild ⊆ A h) (hI : Ichild ⊆ Iv T (j h)) :
    ∀ᵐ p ∂μ, p ∈ Bchild ×ˢ Ichild → p.1 ∈ B h := by
  filter_upwards [ae_unique_dyadic_block ν μ C hμ T, hcover] with p hp hc hchild
  obtain ⟨i, hi, hit⟩ := hc
  have hj : j h = j i := hp _ _ (hI hchild.2) hit
  have heq : h = i := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj h i hne hj) (hsub hchild.1) (hBA i hi)
  simpa only [heq] using hi

/-- The whole child witness floor survives simultaneous fitting to the
ancestor's single affine entry. The measure is the unrestricted law `μ`. -/
lemma child_ancestor_witness_mass {α ι : Type*} [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (C : ENNReal)
    (hμ : μ ≤ C • (ν.prod volume)) (T : ℕ)
    (j : ι → Fin (2 ^ T)) (A B : ι → Set α)
    (hBA : ∀ i, B i ⊆ A i)
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i'))
    (hcover : ∀ᵐ p ∂μ, ∃ i, p.1 ∈ B i ∧ p.2 ∈ Iv T (j i))
    (h : ι) (Bchild : Set α) (Ichild : Set ℝ)
    (hsub : Bchild ⊆ A h) (hI : Ichild ⊆ Iv T (j h)) :
    μ ((Bchild ∩ B h) ×ˢ Ichild) = μ (Bchild ×ˢ Ichild) := by
  apply measure_congr
  filter_upwards [ae_child_mem_ancestor ν μ C hμ T j A B hBA hdisj hcover
    h Bchild Ichild hsub hI] with p hp
  apply propext
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · exact fun h => ⟨⟨h.1, hp h⟩, h.2⟩

end Submission.Obl.k4_horizontal_strict_parameter_step
