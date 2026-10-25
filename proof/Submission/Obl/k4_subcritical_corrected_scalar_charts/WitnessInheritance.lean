/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/WitnessInheritance.lean`. Original attributions are retained below. -/
/- Adapted from this LOT tree, o218, session x0760, commit 55ad73cb9dcb07049bd251578347f6dd43be9caa,
   `Submission/Obl/k4_horizontal_endpoint_wide_return/WitnessInheritance.lean`. -/
/- Generalizes the accepted o238 IncidenceNesting uniqueness API to stand-alone
countable native assignments, using its underlying imported dyadic null lemma. -/

import Submission.Obl.k4_scalar_angular_pair_agreement.Dyadic

set_option autoImplicit false

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open MeasureTheory Set
open Submission.Obl.k4_scalar_angular_pair_agreement
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- Same-block disjoint assignments and the accepted dyadic endpoint-null lemma
provide uniqueness without the critical-rate assumptions of o238's data bundle. -/
theorem true_assignments_ae_unique {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure (α × ℝ)) (c : ENNReal)
    (hdom : μ ≤ c • (ν.prod volume)) (T : ℕ) (j : ι → Fin (2 ^ T)) (A : ι → Set α)
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i')) :
    ∀ᵐ p ∂μ, ∀ i i', p.1 ∈ A i → p.2 ∈ I T (j i) →
      p.1 ∈ A i' → p.2 ∈ I T (j i') → i = i' := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro i'
  by_cases hi : i = i'
  · exact Filter.Eventually.of_forall (fun _ _ _ _ _ => hi)
  by_cases hj : j i = j i'
  · apply Filter.Eventually.of_forall
    intro p hAi hIi hAi' hIi'
    exact (Set.disjoint_left.mp (hdisj i i' hi hj) hAi hAi').elim
  · have hvol := volume_I_inter T hj
    have hnull : μ (univ ×ˢ (I T (j i) ∩ I T (j i'))) = 0 := by
      apply le_antisymm _ zero_le
      calc
        _ ≤ (c • (ν.prod volume)) (univ ×ˢ (I T (j i) ∩ I T (j i'))) := hdom _
        _ = 0 := by simp [Measure.smul_apply, Measure.prod_prod, hvol]
    have hnot : ∀ᵐ p ∂μ, p ∉ univ ×ˢ (I T (j i) ∩ I T (j i')) := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using hnull
    filter_upwards [hnot] with p hp
    intro hAi hIi hAi' hIi'
    exact (hp ⟨mem_univ _, hIi, hIi'⟩).elim

/-- A nested full assignment inherits its named parent's fitted assignment
on almost every original incidence. No selected posterior or new prior appears. -/
theorem nested_assignment_parent_mem {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure (α × ℝ)) (c : ENNReal)
    (hdom : μ ≤ c • (ν.prod volume)) (T : ℕ) (j : ι → Fin (2 ^ T))
    (A B : ι → Set α)
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i'))
    (hBA : ∀ i, B i ⊆ A i)
    (hcover : ∀ᵐ p ∂μ, ∃ i, p.1 ∈ B i ∧ p.2 ∈ I T (j i))
    (C : Set α) (J : Set ℝ) (parent : ι) (hC : C ⊆ A parent) (hJ : J ⊆ I T (j parent)) :
    ∀ᵐ p ∂μ, p.1 ∈ C → p.2 ∈ J → p.1 ∈ B parent := by
  filter_upwards [true_assignments_ae_unique ν μ c hdom T j A hdisj, hcover] with p huniq hcov
  intro hpC hpJ
  obtain ⟨i, hiB, hiI⟩ := hcov
  have hi : i = parent := huniq i parent (hBA i hiB) hiI (hC hpC) (hJ hpJ)
  simpa only [hi] using hiB

/-- The entire original child witness keeps every full-block parent property.
In particular, all-time fits at earlier depths are inherited with exact mass. -/
theorem nested_assignment_original_witness_mass {α ι : Type*}
    [MeasurableSpace α] [Countable ι]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure (α × ℝ)) (c : ENNReal)
    (hdom : μ ≤ c • (ν.prod volume)) (T : ℕ) (j : ι → Fin (2 ^ T))
    (A B : ι → Set α)
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i'))
    (hBA : ∀ i, B i ⊆ A i)
    (hcover : ∀ᵐ p ∂μ, ∃ i, p.1 ∈ B i ∧ p.2 ∈ I T (j i))
    (C : Set α) (J : Set ℝ) (parent : ι) (hC : C ⊆ A parent) (hJ : J ⊆ I T (j parent))
    (P : α → ℝ → Prop) (hP : ∀ l ∈ B parent, ∀ t ∈ I T (j parent), P l t) :
    μ {p | p.1 ∈ C ∧ p.2 ∈ J ∧ ∀ t ∈ J, P p.1 t} = μ (C ×ˢ J) := by
  apply measure_congr
  filter_upwards [nested_assignment_parent_mem ν μ c hdom T j A B hdisj hBA hcover C J parent hC hJ]
    with p hparent
  apply propext
  change (p.1 ∈ C ∧ p.2 ∈ J ∧ ∀ t ∈ J, P p.1 t) ↔ p.1 ∈ C ∧ p.2 ∈ J
  constructor
  · intro hp
    exact ⟨hp.1, hp.2.1⟩
  · rintro ⟨hpC, hpJ⟩
    refine ⟨hpC, hpJ, ?_⟩
    intro t ht
    exact hP p.1 (hparent hpC hpJ) t (hJ ht)

end Submission.Obl.k4_subcritical_corrected_scalar_charts
