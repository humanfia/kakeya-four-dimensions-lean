import Submission.Obl.k4_mk_visibility.NormEllipsoid

namespace Submission.Obl.k4_mk_visibility

open Module MeasureTheory

/-- Inverse seminorm-ball volume controls a determinant. The comparison constant
for directional norms depends only on the dimension. -/
theorem exists_map_of_volume_bound {n : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) (hp : Continuous p)
    (hcoerce : ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ p x) (M : ℝ)
    (hvolume : ENNReal.ofReal M * volume {x | p x ≤ 1} ≤ 1) :
    ∃ A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n),
      M ≤ |LinearMap.det A| ∧ ∀ x, ‖A x‖ ≤ ((n : ℝ) * ((n : ℝ) + 1)) * p x := by
  obtain ⟨A, hA, hvol⟩ := exists_norm_controlled_map p hp hcoerce
  let B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((n : ℝ) + 1) • A
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  have hdet : ENNReal.ofReal |LinearMap.det B| =
      ENNReal.ofReal (((n : ℝ) + 1) ^ n) * ENNReal.ofReal |LinearMap.det A| := by
    dsimp [B]
    rw [LinearMap.det_smul, finrank_euclideanSpace_fin, abs_mul, abs_pow,
      abs_of_pos hpos, ENNReal.ofReal_mul (by positivity)]
  have hcancel : ENNReal.ofReal (((n : ℝ) + 1) ^ n) *
      ENNReal.ofReal (((n : ℝ) + 1)⁻¹ ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow, mul_inv_cancel₀ hpos.ne',
      one_pow, ENNReal.ofReal_one]
  have hsize : 1 ≤ ENNReal.ofReal |LinearMap.det B| * volume {x | p x ≤ 1} := by
    calc
      1 = ENNReal.ofReal (((n : ℝ) + 1) ^ n) *
          ENNReal.ofReal (((n : ℝ) + 1)⁻¹ ^ n) := hcancel.symm
      _ ≤ ENNReal.ofReal (((n : ℝ) + 1) ^ n) *
          (ENNReal.ofReal |LinearMap.det A| * volume {x | p x ≤ 1}) :=
        mul_le_mul_of_nonneg_left hvol zero_le
      _ = ENNReal.ofReal |LinearMap.det B| * volume {x | p x ≤ 1} := by
        rw [← mul_assoc, ← hdet]
  refine ⟨B, ?_, ?_⟩
  · apply (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).mp
    calc
      ENNReal.ofReal M = ENNReal.ofReal M * 1 := (mul_one _).symm
      _ ≤ ENNReal.ofReal M *
          (ENNReal.ofReal |LinearMap.det B| * volume {x | p x ≤ 1}) :=
        mul_le_mul_of_nonneg_left hsize zero_le
      _ = ENNReal.ofReal |LinearMap.det B| *
          (ENNReal.ofReal M * volume {x | p x ≤ 1}) := by ac_rfl
      _ ≤ ENNReal.ofReal |LinearMap.det B| * 1 := mul_le_mul_of_nonneg_left hvolume zero_le
      _ = ENNReal.ofReal |LinearMap.det B| := mul_one _
  · intro x
    change ‖((n : ℝ) + 1) • A x‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    calc
      ((n : ℝ) + 1) * ‖A x‖ ≤ ((n : ℝ) + 1) * ((n : ℝ) * p x) :=
        mul_le_mul_of_nonneg_left (hA x) hpos.le
      _ = ((n : ℝ) * ((n : ℝ) + 1)) * p x := by ring

end Submission.Obl.k4_mk_visibility
