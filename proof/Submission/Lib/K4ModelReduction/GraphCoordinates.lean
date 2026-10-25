import Mathlib

/-! Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper. -/

/-! Spatial coordinates of the graph-time trajectories used in DK4. -/

namespace Submission.Lib.K4ModelReduction

/-- Remove graph-time coordinate zero. -/
def spatialTail {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => x i.succ)

@[simp] theorem spatialTail_apply {n : ℕ}
    (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    spatialTail x i = x i.succ := rfl

@[simp] theorem spatialTail_sub {n : ℕ}
    (x y : EuclideanSpace ℝ (Fin (n + 1))) :
    spatialTail (x - y) = spatialTail x - spatialTail y := by
  ext i
  rfl

/-- The Euclidean decomposition has no loss in the spatial hyperplane. -/
theorem norm_spatialTail_sq {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖x‖ ^ 2 = (x 0) ^ 2 + ‖spatialTail x‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, spatialTail_apply]

theorem norm_spatialTail_le {n : ℕ} (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖spatialTail x‖ ≤ ‖x‖ := by
  nlinarith [norm_spatialTail_sq x, norm_nonneg x, norm_nonneg (spatialTail x),
    sq_nonneg (x 0)]

theorem norm_spatialTail_of_head_zero {n : ℕ}
    (x : EuclideanSpace ℝ (Fin (n + 1))) (hx : x 0 = 0) :
    ‖spatialTail x‖ = ‖x‖ := by
  have h := norm_spatialTail_sq x
  rw [hx] at h
  nlinarith [norm_nonneg x, norm_nonneg (spatialTail x)]

/-- Pairwise separation of graph vectors is exactly spatial-slope separation. -/
theorem dist_spatialTail_of_equal_head {n : ℕ}
    (x y : EuclideanSpace ℝ (Fin (n + 1))) (hxy : x 0 = y 0) :
    dist (spatialTail x) (spatialTail y) = ‖x - y‖ := by
  rw [dist_eq_norm, ← spatialTail_sub]
  exact norm_spatialTail_of_head_zero (x - y) (by simp [hxy])

/-- Insert a graph-time coordinate. -/
def graphLift {n : ℕ} (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 (Fin.cons t (fun i => x i))

@[simp] theorem graphLift_zero {n : ℕ} (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    graphLift t x 0 = t := rfl

@[simp] theorem graphLift_succ {n : ℕ} (t : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (i : Fin n) : graphLift t x i.succ = x i := rfl

@[simp] theorem spatialTail_graphLift {n : ℕ} (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : spatialTail (graphLift t x) = x := by
  ext i
  rfl

@[simp] theorem graphLift_spatialTail {n : ℕ}
    (x : EuclideanSpace ℝ (Fin (n + 1))) : graphLift (x 0) (spatialTail x) = x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem graphLift_isometry {n : ℕ} (t : ℝ) :
    Isometry (fun x : EuclideanSpace ℝ (Fin n) => graphLift t x) := by
  apply Isometry.of_dist_eq
  intro x y
  have h := dist_spatialTail_of_equal_head (graphLift t x) (graphLift t y) rfl
  simpa only [spatialTail_graphLift, dist_eq_norm] using h.symm

theorem graphLift_continuous {n : ℕ} (t : ℝ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) => graphLift t x) :=
  (graphLift_isometry t).continuous

end Submission.Lib.K4ModelReduction
