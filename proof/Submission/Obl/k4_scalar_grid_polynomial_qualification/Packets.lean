import Submission.Obl.k4_fixed_menu_density_pruning.ParentIncidences

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Set MeasureTheory
open Submission.Obl.k4_fixed_menu_density_pruning

/-- Closed time blocks are disjoint away from a null collection of endpoints,
so the frozen packet disjointness gives an unambiguous original packet label. -/
theorem packet_index_unique_at_interior {α Γ : Type*} {n T : ℕ}
    (γ : Fin n → Γ) (j : Fin n → Fin (2 ^ T)) (A : Fin n → Set α)
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i'))
    {i i' : Fin n} {p : α × ℝ}
    (hworld : γ i = γ i') (hA : p.1 ∈ A i) (hA' : p.1 ∈ A i')
    (ht : p.2 ∈ Ioo (((j i : ℕ) : ℝ) / (2 : ℝ) ^ T)
      ((((j i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T))
    (ht' : p.2 ∈ Icc (((j i' : ℕ) : ℝ) / (2 : ℝ) ^ T)
      ((((j i' : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)) : i = i' := by
  have hj : j i = j i' := Fin.ext (time_cell_unique (by positivity) ht ht')
  by_contra hne
  exact Set.disjoint_left.mp (hdisj i i' hne hworld hj) hA hA'

/-- Every one of finitely many packet time memberships can be changed from
closed to open under any law absolutely continuous with respect to prior time. -/
theorem ae_packet_membership_interior {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (hμ : μ ≪ ν.prod volume)
    {n T : ℕ} (j : Fin n → Fin (2 ^ T)) :
    ∀ᵐ p ∂μ, ∀ i : Fin n,
      p.2 ∈ Icc (((j i : ℕ) : ℝ) / (2 : ℝ) ^ T)
          ((((j i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) →
      p.2 ∈ Ioo (((j i : ℕ) : ℝ) / (2 : ℝ) ^ T)
          ((((j i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) := by
  apply hμ.ae_le
  apply ae_all_iff.mpr
  intro i
  filter_upwards [ae_time_ne ν (((j i : ℕ) : ℝ) / (2 : ℝ) ^ T),
    ae_time_ne ν ((((j i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)] with p hlo hhi hp
  exact ⟨lt_of_le_of_ne hp.1 hlo.symm, lt_of_le_of_ne hp.2 hhi⟩

/-- The packets through an original incidence have a unique label almost
everywhere, before any discovery restriction or choice of polynomial. -/
theorem ae_packet_index_unique {α Γ : Type*} [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (hμ : μ ≪ ν.prod volume)
    {n T : ℕ} (γ : Fin n → Γ) (j : Fin n → Fin (2 ^ T)) (A : Fin n → Set α)
    (hdisj : ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i')) :
    ∀ᵐ p ∂μ, ∀ i i', γ i = γ i' → p.1 ∈ A i → p.1 ∈ A i' →
      p.2 ∈ Icc (((j i : ℕ) : ℝ) / (2 : ℝ) ^ T)
          ((((j i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) →
      p.2 ∈ Icc (((j i' : ℕ) : ℝ) / (2 : ℝ) ^ T)
          ((((j i' : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T) → i = i' := by
  filter_upwards [ae_packet_membership_interior ν μ hμ j] with p hp
  intro i i' hg ha ha' ht ht'
  exact packet_index_unique_at_interior γ j A hdisj hg ha ha' (hp i ht) ht'

end Submission.Obl.k4_scalar_grid_polynomial_qualification
