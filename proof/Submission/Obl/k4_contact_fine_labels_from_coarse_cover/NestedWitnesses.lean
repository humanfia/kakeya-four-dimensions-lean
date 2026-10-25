-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/NestedWitnesses.lean
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.ModelBounds
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.MeshVelocity

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open MeasureTheory Set Filter

/-- Original prior-times-time domination removes every endpoint of one
dyadic grid, simultaneously for all labels at that depth. -/
theorem ae_time_away_from_endpoints {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (ν : Measure α) [IsProbabilityMeasure ν]
    (C : ENNReal) (hdom : μ ≤ C • (ν.prod volume)) (T : ℕ) :
    ∀ᵐ p ∂μ, ∀ a : ℤ, p.2 ≠ (a : ℝ) / (2 : ℝ) ^ T := by
  apply ae_all_iff.mpr
  intro a
  apply ae_iff.mpr
  simp only [not_not]
  have heq : {p : α × ℝ | p.2 = (a : ℝ) / (2 : ℝ) ^ T} =
      univ ×ˢ {(a : ℝ) / (2 : ℝ) ^ T} := by ext p; simp
  rw [heq]
  apply le_antisymm ((hdom _).trans ?_) bot_le
  simp [Measure.smul_apply, smul_eq_mul, Measure.prod_prod]

/-- Closed dyadic blocks have a unique index away from their endpoints. -/
theorem timeBlock_index_unique (T : ℕ) (j j' : Fin (2 ^ T)) (t : ℝ)
    (ht : t ∈ timeBlock T j) (ht' : t ∈ timeBlock T j')
    (hne : ∀ a : ℤ, t ≠ (a : ℝ) / (2 : ℝ) ^ T) : j = j' := by
  have hD : 0 < (2 : ℝ) ^ T := by positivity
  have hfloor (i : Fin (2 ^ T)) (hi : t ∈ timeBlock T i) :
      ⌊t * (2 : ℝ) ^ T⌋ = ((i : ℕ) : ℤ) := by
    change (i : ℕ) / (2 : ℝ) ^ T ≤ t ∧ t ≤ ((i : ℕ) + 1) / (2 : ℝ) ^ T at hi
    apply Int.floor_eq_iff.mpr
    constructor
    · exact_mod_cast (div_le_iff₀ hD).mp hi.1
    · have hstrict : t < ((i : ℕ) + 1) / (2 : ℝ) ^ T := by
        apply lt_of_le_of_ne hi.2
        simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using hne ((i : ℕ) + 1)
      exact_mod_cast (lt_div_iff₀ hD).mp hstrict
  have hj : ((j : ℕ) : ℤ) = ((j' : ℕ) : ℤ) := (hfloor j ht).symm.trans (hfloor j' ht')
  apply Fin.ext
  exact_mod_cast hj

/-- The original shallow cover and assignment disjointness identify the
true parent of almost every deep incidence. The witnesses consequently lie
in the shallow B-assignment, where the shallow whole-block fit is stored. -/
theorem ae_child_in_true_parent {α ι : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (ν : Measure α) [IsProbabilityMeasure ν]
    (C : ENNReal) (hdom : μ ≤ C • (ν.prod volume)) {n T : ℕ}
    (j : Fin n → Fin (2 ^ T)) (A B : Fin n → Set α)
    (hBA : ∀ i, B i ⊆ A i)
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i'))
    (hcover : ∀ᵐ p ∂μ, ∃ i, p.1 ∈ B i ∧ p.2 ∈ timeBlock T (j i))
    (child : ι → Set α) (J : ι → Set ℝ) (parent : ι → Fin n)
    (hsub : ∀ u, child u ⊆ A (parent u))
    (hJ : ∀ u, J u ⊆ timeBlock T (j (parent u))) :
    ∀ᵐ p ∂μ, ∀ u, p.1 ∈ child u → p.2 ∈ J u → p.1 ∈ B (parent u) := by
  filter_upwards [hcover, ae_time_away_from_endpoints μ ν C hdom T] with p hp htime
  obtain ⟨i, hi, hti⟩ := hp
  intro u hu htu
  have hj : j (parent u) = j i := timeBlock_index_unique T _ _ p.2 (hJ u htu) hti htime
  have heq : parent u = i := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj (parent u) i hne hj)
      (hsub u hu) (hBA i hi)
  simpa only [heq] using hi

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
