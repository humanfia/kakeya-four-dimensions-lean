import Mathlib
import Submission.Obl.k4_scalar_coefficient_clustering.Input

namespace Submission.Obl.k4_plank_projected_multiplicity

abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev E3 := EuclideanSpace ℝ (Fin 3)

abbrev PlankEstimate : Prop := Submission.Obl.k4_scalar_coefficient_clustering.PlankInput

theorem trajectory_norm_le {A : ℝ} (hA : 0 ≤ A) (x : E3)
    (hx : ∀ i, |x i| ≤ A) : ‖x‖ ≤ 3 * A := by
  have hsq (i : Fin 3) : (x i) ^ 2 ≤ A ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x i)) (hx i) 2
  apply (sq_le_sq₀ (norm_nonneg x) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_three]
  nlinarith [hsq 0, hsq 1, hsq 2]

end Submission.Obl.k4_plank_projected_multiplicity
