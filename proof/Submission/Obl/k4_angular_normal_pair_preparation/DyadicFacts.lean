import Submission.Obl.k4_angular_normal_pair_preparation.Definitions
import Submission.Obl.k4_scalar_angular_pair_agreement.Dyadic

namespace Submission.Obl.k4_angular_normal_pair_preparation

open MeasureTheory Set

/-- A fine time block is contained in the interval selected by its integer quotient. -/
theorem fine_subset_coarse (T s : ℕ) (j : Fin (2 ^ (T + s))) :
    Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ (T + s))
      ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (T + s)) ⊆ coarseInterval T s j := by
  have hle : T ≤ T + s := Nat.le_add_right _ _
  obtain ⟨b, hb⟩ := Submission.Obl.k4_scalar_angular_pair_agreement.exists_coarse hle j
  have hi := (Submission.Obl.k4_scalar_angular_pair_agreement.I_subset_iff hle j b).mp hb
  have hbval : (b : ℕ) = (j : ℕ) / 2 ^ s := by simpa using hi.symm
  simpa only [Submission.Obl.k4_scalar_linear_critical_extremizers.Split.I,
    coarseInterval, hbval] using hb

/-- The endpoints of a fine block lie within the coarse interval. -/
theorem fine_coarse_endpoints (T s : ℕ) (j : Fin (2 ^ (T + s))) :
    (((j : ℕ) / 2 ^ s : ℕ) : ℝ) / (2 : ℝ) ^ T ≤
        ((j : ℕ) : ℝ) / (2 : ℝ) ^ (T + s) ∧
    ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (T + s)) ≤
        ((((j : ℕ) / 2 ^ s : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T := by
  have hlo : ((j : ℕ) : ℝ) / (2 : ℝ) ^ (T + s) ≤
      (((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (T + s) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  exact ⟨(fine_subset_coarse T s j ⟨le_rfl, hlo⟩).1,
    (fine_subset_coarse T s j ⟨hlo, le_rfl⟩).2⟩

/-- The coarse interval has its exact dyadic length, without endpoint mass. -/
theorem volume_coarseInterval (T s j : ℕ) :
    volume (coarseInterval T s j) = ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹) := by
  rw [coarseInterval, Real.volume_Icc]
  congr 1
  field_simp
  ring

end Submission.Obl.k4_angular_normal_pair_preparation
