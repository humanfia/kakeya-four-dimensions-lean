/- Adapted from this LOT tree, o144, session x0488, commit 5ed40f2, Submission/Obl/k4_seven_direction_local_degree_restoration/TaylorConic.lean. -/
import Submission.Obl.k4_approximate_conic_taylor_decomposition.Taylor

namespace Submission.Obl.k4_approximate_conic_taylor_decomposition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Assemble the cubic and quartic kernel approximations using a fifth-order Taylor remainder. -/
theorem conic_taylor_error_le {R q ell : E → ℝ} {lam B3 B4 B5 : ℝ}
    (hR : ContDiffOn ℝ 5 R (Metric.ball (0 : E) 3))
    (h5 : ∀ u ∈ Metric.closedBall (0 : E) 1, ‖iteratedFDeriv ℝ 5 R u‖ ≤ B5)
    (h3 : ∀ u ∈ Metric.closedBall (0 : E) 1,
      |iteratedFDeriv ℝ 3 R 0 (fun _ => u) / 6 - q u * ell u| ≤ B3)
    (h4 : ∀ u ∈ Metric.closedBall (0 : E) 1,
      |iteratedFDeriv ℝ 4 R 0 (fun _ => u) / 24 - lam * (q u) ^ 2| ≤ B4)
    {u : E} (hu : u ∈ Metric.closedBall (0 : E) 1) :
    |R u - (R 0 + fderiv ℝ R 0 u + iteratedFDeriv ℝ 2 R 0 (fun _ => u) / 2 +
      q u * ell u + lam * (q u) ^ 2)| ≤ B5 / 120 + B3 + B4 := by
  have ht := abs_sub_radial_taylor_le (by norm_num : 0 < 5) hR h5 hu
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply] at ht
  norm_num [Nat.factorial] at ht
  let T := R 0 + fderiv ℝ R 0 u + iteratedFDeriv ℝ 2 R 0 (fun _ => u) / 2
  let F3 := iteratedFDeriv ℝ 3 R 0 (fun _ => u) / 6
  let F4 := iteratedFDeriv ℝ 4 R 0 (fun _ => u) / 24
  have he : R u - (T + q u * ell u + lam * (q u) ^ 2) =
      (R u - (T + F3 + F4)) + (F3 - q u * ell u) + (F4 - lam * (q u) ^ 2) := by ring
  change |R u - (T + q u * ell u + lam * (q u) ^ 2)| ≤ _
  rw [he]
  have hsum := abs_add_le ((R u - (T + F3 + F4)) + (F3 - q u * ell u))
    (F4 - lam * (q u) ^ 2)
  have hsum' := abs_add_le (R u - (T + F3 + F4)) (F3 - q u * ell u)
  have ht' : |R u - (T + F3 + F4)| ≤ B5 / 120 := ht
  linarith only [hsum, hsum', ht', h3 u hu, h4 u hu]

/-- The same assembly using only diagonal fifth-derivative contractions on radial segments. -/
theorem conic_taylor_diagonal_error_le {R q ell : E → ℝ} {lam B3 B4 B5 : ℝ}
    (hR : ContDiffOn ℝ 5 R (Metric.ball (0 : E) 3))
    (h5 : ∀ u ∈ Metric.closedBall (0 : E) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |iteratedFDeriv ℝ 5 R (t • u) (fun _ => u)| ≤ B5)
    (h3 : ∀ u ∈ Metric.closedBall (0 : E) 1,
      |iteratedFDeriv ℝ 3 R 0 (fun _ => u) / 6 - q u * ell u| ≤ B3)
    (h4 : ∀ u ∈ Metric.closedBall (0 : E) 1,
      |iteratedFDeriv ℝ 4 R 0 (fun _ => u) / 24 - lam * (q u) ^ 2| ≤ B4)
    {u : E} (hu : u ∈ Metric.closedBall (0 : E) 1) :
    |R u - (R 0 + fderiv ℝ R 0 u + iteratedFDeriv ℝ 2 R 0 (fun _ => u) / 2 +
      q u * ell u + lam * (q u) ^ 2)| ≤ B5 / 120 + B3 + B4 := by
  have ht := abs_sub_radial_taylor_le_diagonal (by norm_num : 0 < 5) hR hu (h5 u hu)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply] at ht
  norm_num [Nat.factorial] at ht
  let T := R 0 + fderiv ℝ R 0 u + iteratedFDeriv ℝ 2 R 0 (fun _ => u) / 2
  let F3 := iteratedFDeriv ℝ 3 R 0 (fun _ => u) / 6
  let F4 := iteratedFDeriv ℝ 4 R 0 (fun _ => u) / 24
  have he : R u - (T + q u * ell u + lam * (q u) ^ 2) =
      (R u - (T + F3 + F4)) + (F3 - q u * ell u) + (F4 - lam * (q u) ^ 2) := by ring
  change |R u - (T + q u * ell u + lam * (q u) ^ 2)| ≤ _
  rw [he]
  have hsum := abs_add_le ((R u - (T + F3 + F4)) + (F3 - q u * ell u))
    (F4 - lam * (q u) ^ 2)
  have hsum' := abs_add_le (R u - (T + F3 + F4)) (F3 - q u * ell u)
  have ht' : |R u - (T + F3 + F4)| ≤ B5 / 120 := ht
  linarith only [hsum, hsum', ht', h3 u hu, h4 u hu]

end Submission.Obl.k4_approximate_conic_taylor_decomposition
