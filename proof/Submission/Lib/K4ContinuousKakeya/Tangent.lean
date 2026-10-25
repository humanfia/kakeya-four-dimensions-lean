import Submission.Lib.K4ContinuousKakeya.Continuous

set_option linter.unusedVariables false

/-!
# Tangent lines of quadratic trajectories

For `y = y₀ + V t` and `X = x₀ + x₁ t + x₂ t²`, the physical point `(t, y, X)` deviates from the
tangent line at time `c` by exactly `|x₂| (t - c)²`, and the lifted velocity `(1, V, X')` moves by
`2 |x₂| |t - c|`; normalizing vectors of norm at least one is `2`-Lipschitz. These are the curve
linearization errors of the velocity-graph Kakeya argument (paper `a05:velocity-graph`).
-/

namespace Submission.Lib.K4ContinuousKakeya

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The physical point `(t, y(t), X(t))` of a trajectory with `y = y₀ + V t` and
`X = x₀ + x₁ t + x₂ t²`. -/
def physPoint (y₀ V x₀ x₁ x₂ t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![t, y₀ + V * t, x₀ + x₁ * t + x₂ * t ^ 2]

/-- The lifted velocity `(1, V, X'(t))` of that trajectory. -/
def liftVel (V x₁ x₂ t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![1, V, x₁ + 2 * x₂ * t]

/-- The deviation of the trajectory from its tangent line at `c` is `x₂ (t - c)²` in the hidden
coordinate only. -/
lemma physPoint_sub_tangent (y₀ V x₀ x₁ x₂ c t : ℝ) :
    physPoint y₀ V x₀ x₁ x₂ t - (physPoint y₀ V x₀ x₁ x₂ c + (t - c) • liftVel V x₁ x₂ c) =
      WithLp.toLp 2 ![0, 0, x₂ * (t - c) ^ 2] := by
  ext i
  fin_cases i <;> simp [physPoint, liftVel] <;> ring

lemma norm_physPoint_sub_tangent (y₀ V x₀ x₁ x₂ c t : ℝ) :
    ‖physPoint y₀ V x₀ x₁ x₂ t - (physPoint y₀ V x₀ x₁ x₂ c + (t - c) • liftVel V x₁ x₂ c)‖ =
      |x₂| * (t - c) ^ 2 := by
  rw [physPoint_sub_tangent, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_three, Real.sqrt_sq_eq_abs, abs_mul, sq_abs]

lemma liftVel_sub (V x₁ x₂ c t : ℝ) :
    liftVel V x₁ x₂ t - liftVel V x₁ x₂ c = WithLp.toLp 2 ![0, 0, 2 * x₂ * (t - c)] := by
  ext i
  fin_cases i <;> simp [liftVel]; ring

lemma norm_liftVel_sub (V x₁ x₂ c t : ℝ) :
    ‖liftVel V x₁ x₂ t - liftVel V x₁ x₂ c‖ = 2 * |x₂| * |t - c| := by
  rw [liftVel_sub, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_three, Real.sqrt_sq_eq_abs, abs_mul]

lemma one_le_norm_liftVel (V x₁ x₂ t : ℝ) : 1 ≤ ‖liftVel V x₁ x₂ t‖ := by
  have h := abs_apply_le_norm (liftVel V x₁ x₂ t) 0
  simpa [liftVel] using h

/-- Normalizing vectors of norm at least one is `2`-Lipschitz. -/
lemma norm_normalize_sub_le {n : ℕ} {p q : EuclideanSpace ℝ (Fin n)} (hq : 1 ≤ ‖q‖)
    (hp : 1 ≤ ‖p‖) : ‖‖p‖⁻¹ • p - ‖q‖⁻¹ • q‖ ≤ 2 * ‖p - q‖ := by
  have hp0 : 0 < ‖p‖ := lt_of_lt_of_le one_pos hp
  have hq0 : 0 < ‖q‖ := lt_of_lt_of_le one_pos hq
  have key : ‖p‖⁻¹ • p - ‖q‖⁻¹ • q = ‖p‖⁻¹ • (p - q) + (‖p‖⁻¹ - ‖q‖⁻¹) • q := by
    rw [smul_sub, sub_smul]; abel
  rw [key]
  calc ‖‖p‖⁻¹ • (p - q) + (‖p‖⁻¹ - ‖q‖⁻¹) • q‖
      ≤ ‖‖p‖⁻¹ • (p - q)‖ + ‖(‖p‖⁻¹ - ‖q‖⁻¹) • q‖ := norm_add_le _ _
    _ = ‖p‖⁻¹ * ‖p - q‖ + |‖p‖⁻¹ - ‖q‖⁻¹| * ‖q‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp0)]
    _ ≤ ‖p - q‖ + ‖p - q‖ := by
        gcongr
        · calc ‖p‖⁻¹ * ‖p - q‖ ≤ 1 * ‖p - q‖ := by
                gcongr
                exact inv_le_one_of_one_le₀ hp
            _ = ‖p - q‖ := one_mul _
        · have h1 : |‖p‖⁻¹ - ‖q‖⁻¹| * ‖q‖ = |‖q‖ - ‖p‖| / ‖p‖ := by
            rw [inv_sub_inv hp0.ne' hq0.ne', abs_div, abs_mul, abs_of_pos hp0, abs_of_pos hq0]
            field_simp
          rw [h1, div_le_iff₀ hp0]
          calc |‖q‖ - ‖p‖| ≤ ‖q - p‖ := abs_norm_sub_norm_le q p
            _ = ‖p - q‖ := norm_sub_rev q p
            _ ≤ ‖p - q‖ * ‖p‖ := le_mul_of_one_le_right (norm_nonneg _) hp
    _ = 2 * ‖p - q‖ := by ring

/-- The trajectory point at time `t` lies in the tube of radius `r` about its tangent line at
`c` (unit direction), as soon as `|x₂| (t - c)² < r`. -/
lemma physPoint_mem_tube_tangent (y₀ V x₀ x₁ x₂ c t r : ℝ) (h : |x₂| * (t - c) ^ 2 < r) :
    physPoint y₀ V x₀ x₁ x₂ t ∈ tube r (physPoint y₀ V x₀ x₁ x₂ c)
      (‖liftVel V x₁ x₂ c‖⁻¹ • liftVel V x₁ x₂ c) := by
  apply Metric.mem_thickening_iff.mpr
  refine ⟨physPoint y₀ V x₀ x₁ x₂ c + ((t - c) * ‖liftVel V x₁ x₂ c‖) •
      (‖liftVel V x₁ x₂ c‖⁻¹ • liftVel V x₁ x₂ c), ⟨_, rfl⟩, ?_⟩
  have hn : ‖liftVel V x₁ x₂ c‖ ≠ 0 :=
    (lt_of_lt_of_le one_pos (one_le_norm_liftVel V x₁ x₂ c)).ne'
  rw [smul_smul, mul_assoc, mul_inv_cancel₀ hn, mul_one, dist_eq_norm,
    norm_physPoint_sub_tangent]
  exact h

end

end Submission.Lib.K4ContinuousKakeya
