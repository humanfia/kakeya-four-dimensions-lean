import Mathlib

namespace Submission.Obl.k4_scalar_initial_true_horizon

/-- A uniform real cardinal bound on finite subfamilies forces finiteness. -/
theorem finite_of_uniform_finset_card_bound {ι : Type*} (S : Set ι) (C : ℝ)
    (hcount : ∀ F : Finset ι, (↑F : Set ι) ⊆ S → (F.card : ℝ) ≤ C) : S.Finite := by
  classical
  by_contra hinf
  have hInf : S.Infinite := hinf
  obtain ⟨n, hn⟩ := exists_nat_gt C
  obtain ⟨F, hFS, hcard⟩ := hInf.exists_subset_card_eq n
  have hbound := hcount F hFS
  rw [hcard] at hbound
  exact (not_le_of_gt hn) hbound

end Submission.Obl.k4_scalar_initial_true_horizon
