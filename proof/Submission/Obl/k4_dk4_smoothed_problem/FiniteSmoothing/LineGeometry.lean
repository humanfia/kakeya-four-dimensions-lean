/- Adapted within this LOT tree from o006/x0006, Submission/Obl/k4_core/FiniteSmoothing/LineGeometry.lean.
Original o018/x0048 attribution is retained below. -/

/- Adapted from the same LOT tree, obligation o018, session x0048, commit 6d775765b92912e6ea3c223ec01500dda1f728e5,
Submission/Obl/k4_framework_from_matching_clustering_conic/LineGeometry.lean. Namespace and own-submodule import paths changed; proof content retained. -/

import Submission.Obl.k4_lower_of_discrete.Localization

/-! Geometry of perturbing the three intercept and three slope coordinates in
the smoothing paragraph of Theorem 2.17. -/

open Set Metric

namespace Submission.Obl.k4_dk4_smoothed_problem.FiniteSmoothing

/-- The three spatial coordinates in the graph convention used by DK4. -/
noncomputable def spatialCoords (x : EuclideanSpace ℝ (Fin 4)) : Fin 3 → ℝ :=
  ![x 1, x 2, x 3]

theorem norm_spatialCoords_le (x : EuclideanSpace ℝ (Fin 4)) :
    ‖WithLp.toLp 2 (spatialCoords x)‖ ≤ ‖x‖ := by
  have hx := EuclideanSpace.real_norm_sq_eq x
  have hs : ‖WithLp.toLp 2 (spatialCoords x)‖ ^ 2 = (x 1)^2 + (x 2)^2 + (x 3)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [spatialCoords, Fin.sum_univ_succ]
    ring
  simp [Fin.sum_univ_succ] at hx
  nlinarith [sq_nonneg (x 0), norm_nonneg x, norm_nonneg (WithLp.toLp 2 (spatialCoords x))]

theorem slopeVec_spatialCoords {x : EuclideanSpace ℝ (Fin 4)} (hx : x 0 = 1) :
    Submission.Obl.k4_lower_of_discrete.slopeVec (WithLp.toLp 2 (spatialCoords x)) = x := by
  ext j
  fin_cases j <;>
    simp [spatialCoords, Submission.Obl.k4_lower_of_discrete.slopeVec, hx]

theorem norm_spatialCoords_sub {x y : EuclideanSpace ℝ (Fin 4)}
    (hx : x 0 = 1) (hy : y 0 = 1) :
    ‖WithLp.toLp 2 (spatialCoords x) - WithLp.toLp 2 (spatialCoords y)‖ = ‖x - y‖ := by
  rw [← Submission.Obl.k4_lower_of_discrete.norm_slopeVec_sub,
    slopeVec_spatialCoords hx, slopeVec_spatialCoords hy]

/-- An affine trajectory in graph coordinates. -/
noncomputable def graphLine (b s : Fin 3 → ℝ) (t : ℝ) :
    EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![t, b 0 + t * s 0, b 1 + t * s 1, b 2 + t * s 2]

theorem graphLine_spatialCoords {x v : EuclideanSpace ℝ (Fin 4)}
    (hx : x 0 = 0) (hv : v 0 = 1) (t : ℝ) :
    graphLine (spatialCoords x) (spatialCoords v) t = x + t • v := by
  ext j
  fin_cases j <;> simp [graphLine, spatialCoords, hx, hv]

theorem continuous_graphLine : Continuous
    (fun p : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × ℝ =>
      graphLine p.1.1 p.1.2 p.2) := by
  unfold graphLine
  fun_prop

/-- The three-coordinate Euclidean norm is bounded by three coordinate bounds. -/
theorem norm_toLp_three_le {z : Fin 3 → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hz : ∀ j, |z j| ≤ r) : ‖WithLp.toLp 2 z‖ ≤ 3 * r := by
  have hsq (j : Fin 3) : (z j) ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (z j)) hr).mpr (hz j)
  have hnorm := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 z)
  simp [Fin.sum_univ_succ] at hnorm
  nlinarith [hsq 0, hsq 1, hsq 2, norm_nonneg (WithLp.toLp 2 z), sq_nonneg r]

theorem graphLine_same_time_norm (b s b' s' : Fin 3 → ℝ) (t : ℝ) :
    ‖graphLine b s t - graphLine b' s' t‖ =
      ‖WithLp.toLp 2 (fun j => (b j - b' j) + t * (s j - s' j))‖ := by
  have heq : graphLine b s t - graphLine b' s' t =
      Submission.Obl.k4_lower_of_discrete.slopeVec
        (WithLp.toLp 2 (fun j => b j + t * s j)) -
      Submission.Obl.k4_lower_of_discrete.slopeVec
        (WithLp.toLp 2 (fun j => b' j + t * s' j)) := by
    ext j
    fin_cases j <;> simp [graphLine, Submission.Obl.k4_lower_of_discrete.slopeVec]
  rw [heq, Submission.Obl.k4_lower_of_discrete.norm_slopeVec_sub]
  congr 1
  ext j
  simp
  ring

theorem graphLine_perturbation_le {r : ℝ} (hr : 0 ≤ r)
    {b s b' s' : Fin 3 → ℝ}
    (hb : ∀ j, |b j - b' j| ≤ r) (hs : ∀ j, |s j - s' j| ≤ r)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖graphLine b s t - graphLine b' s' t‖ ≤ 6 * r := by
  rw [graphLine_same_time_norm]
  calc
    ‖WithLp.toLp 2 (fun j => (b j - b' j) + t * (s j - s' j))‖ ≤ 3 * (2 * r) := by
      apply norm_toLp_three_le (by positivity)
      intro j
      calc
        |(b j - b' j) + t * (s j - s' j)| ≤
            |b j - b' j| + |t * (s j - s' j)| := abs_add_le _ _
        _ ≤ r + r := by
          rw [abs_mul, abs_of_nonneg ht.1]
          exact add_le_add (hb j) ((mul_le_mul_of_nonneg_left (hs j) ht.1).trans
            (mul_le_of_le_one_left hr ht.2))
        _ = 2 * r := by ring
    _ = 6 * r := by ring

/-- A covered time survives every permitted perturbation after enlarging the ball radius. -/
theorem graphLine_perturbation_mem_ball {r ρ : ℝ} (hr : 0 ≤ r)
    {b s b' s' : Fin 3 → ℝ}
    (hb : ∀ j, |b j - b' j| ≤ r) (hs : ∀ j, |s j - s' j| ≤ r)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {z : EuclideanSpace ℝ (Fin 4)}
    (hz : graphLine b' s' t ∈ ball z ρ) :
    graphLine b s t ∈ ball z (ρ + 6 * r) := by
  rw [mem_ball] at hz ⊢
  calc
    dist (graphLine b s t) z ≤
        dist (graphLine b s t) (graphLine b' s' t) + dist (graphLine b' s' t) z :=
      dist_triangle _ _ _
    _ < 6 * r + ρ := add_lt_add_of_le_of_lt
      (by simpa [dist_eq_norm] using graphLine_perturbation_le hr hb hs ht) hz
    _ = ρ + 6 * r := add_comm _ _

end Submission.Obl.k4_dk4_smoothed_problem.FiniteSmoothing
