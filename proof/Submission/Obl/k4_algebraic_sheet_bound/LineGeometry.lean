import Mathlib

namespace Submission.Obl.k4_algebraic_sheet_bound

open Set Metric

/-- Embedding the real coordinate slice into complex Euclidean space preserves its norm. -/
theorem norm_complexify {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖(WithLp.toLp 2 (fun i : Fin n => (x i : ℂ)) : EuclideanSpace ℂ (Fin n))‖ = ‖x‖ := by
  simp only [EuclideanSpace.norm_eq, Complex.norm_real,
    Real.norm_eq_abs]

/-- The disk needed for continuation lies strictly inside the sheet's holomorphic domain. -/
theorem affine_line_mem_ball_four {n : ℕ} {x z : EuclideanSpace ℂ (Fin n)}
    (hx : ‖x‖ ≤ (1 : ℝ) / 2) (hz : ‖z‖ ≤ 1) {t : ℂ} (ht : t ∈ ball 0 2) :
    x + t • (z - x) ∈ ball (0 : EuclideanSpace ℂ (Fin n)) 4 := by
  rw [mem_ball, dist_zero_right] at ht ⊢
  have hd : ‖z - x‖ ≤ 3 / 2 := by
    calc
      ‖z - x‖ ≤ ‖z‖ + ‖x‖ := norm_sub_le z x
      _ ≤ 3 / 2 := by linarith
  calc
    ‖x + t • (z - x)‖ ≤ ‖x‖ + ‖t • (z - x)‖ := norm_add_le _ _
    _ = ‖x‖ + ‖t‖ * ‖z - x‖ := by rw [norm_smul]
    _ ≤ 1 / 2 + 2 * (3 / 2) := by gcongr
    _ < 4 := by norm_num

/-- Affine restrictions of sheets are holomorphic on the disk used in the stability lemma. -/
theorem differentiableOn_affine_line {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 4)) {x z : EuclideanSpace ℂ (Fin n)}
    (hx : ‖x‖ ≤ (1 : ℝ) / 2) (hz : ‖z‖ ≤ 1) :
    DifferentiableOn ℂ (fun t : ℂ => f (x + t • (z - x))) (ball 0 2) := by
  apply hf.comp ((differentiable_const _).add
    (differentiable_id.smul_const (z - x))).differentiableOn
  exact fun t ht => affine_line_mem_ball_four hx hz ht

end Submission.Obl.k4_algebraic_sheet_bound
