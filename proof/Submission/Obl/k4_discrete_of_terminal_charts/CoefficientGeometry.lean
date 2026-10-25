import Submission.Obl.k4_discrete_of_terminal_charts.SlopeComparison

namespace Submission.Obl.k4_discrete_of_terminal_charts

noncomputable section

abbrev Trajectory := ℕ × (Fin 6 → ℝ)

def trajectoryIntercept (l : Trajectory) : E3 := WithLp.toLp 2 ![l.2 0, l.2 1, l.2 2]

def trajectorySlope (l : Trajectory) : E3 := WithLp.toLp 2 ![l.2 3, l.2 4, l.2 5]

theorem trajectory_point (l : Trajectory) (t : ℝ) :
    ![t, (trajectoryIntercept l + t • trajectorySlope l) 0,
      (trajectoryIntercept l + t • trajectorySlope l) 1,
      (trajectoryIntercept l + t • trajectorySlope l) 2] =
      ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] := rfl

theorem trajectory_planar_delta (l : Trajectory) (t : ℝ) (c u : E2) :
    WithLp.toLp 2 (fun i : Fin 2 =>
      (trajectoryIntercept l + t • trajectorySlope l) i.castSucc - c i - t * u i) =
      WithLp.toLp 2 ![l.2 0 + t * l.2 3, l.2 1 + t * l.2 4] - c - t • u := by
  ext i
  fin_cases i <;> rfl

theorem trajectory_norm_le {A : ℝ} (hA : 0 ≤ A) (x : E3)
    (hx : ∀ i, |x i| ≤ A) : ‖x‖ ≤ 3 * A := by
  have hsq (i : Fin 3) : (x i) ^ 2 ≤ A ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x i)) (hx i) 2
  apply (sq_le_sq₀ (norm_nonneg x) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_three]
  nlinarith [hsq 0, hsq 1, hsq 2]

theorem trajectoryIntercept_norm_le {A : ℝ} (hA : 0 ≤ A) (l : Trajectory)
    (hl : ∀ i, |l.2 i| ≤ A) : ‖trajectoryIntercept l‖ ≤ 3 * A := by
  apply trajectory_norm_le hA
  intro i
  fin_cases i <;> simpa [trajectoryIntercept] using hl _

theorem trajectorySlope_norm_le {A : ℝ} (hA : 0 ≤ A) (l : Trajectory)
    (hl : ∀ i, |l.2 i| ≤ A) : ‖trajectorySlope l‖ ≤ 3 * A := by
  apply trajectory_norm_le hA
  intro i
  fin_cases i <;> simpa [trajectorySlope] using hl _

def gridWidth (N r : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(⌊r * Real.log N / Real.log 2⌋ : ℤ))

theorem gridWidth_pos (N r : ℝ) : 0 < gridWidth N r := by
  unfold gridWidth
  positivity

/-- Replacing a power mesh by its dyadic rounding costs at most a factor of two. -/
theorem gridWidth_le {N r : ℝ} (hN : 0 < N) : gridWidth N r ≤ 2 * N ^ (-r) := by
  have heq : (2 : ℝ) ^ (r * Real.log N / Real.log 2) = N ^ r := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos hN]
    congr 1
    field_simp
  have hfloor : -(⌊r * Real.log N / Real.log 2⌋ : ℝ) ≤
      1 - r * Real.log N / Real.log 2 := by
    have := Int.lt_floor_add_one (r * Real.log N / Real.log 2)
    linarith
  calc
    gridWidth N r = (2 : ℝ) ^ (-(⌊r * Real.log N / Real.log 2⌋ : ℝ)) := by
      rw [gridWidth, ← Real.rpow_intCast]
      simp
    _ ≤ (2 : ℝ) ^ (1 - r * Real.log N / Real.log 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor
    _ = 2 * N ^ (-r) := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_one, heq, Real.rpow_neg hN.le]
      exact div_eq_mul_inv _ _

end

end Submission.Obl.k4_discrete_of_terminal_charts
