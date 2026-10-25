/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, NativeRowField.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.NativePrimitive

/-! Adapted from our LOT tree o107, session x0353, AffineRowField.lean
(commit 2d33b59a). These identities use physical derivative units. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory

def nativeHorizontalPoint (b : Fin 6 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![t, b 0 + t * b 3, b 1 + t * b 4]

def horizontalAffineRow (A : Fin 4 → ℝ) (q : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![A 1 - q 1 * A 3, A 2 + q 0 * A 3]

theorem measurable_horizontalAffineRow
    {Y : Type*} [MeasurableSpace Y] (A : Y → Fin 4 → ℝ) (q : Y → Fin 3 → ℝ)
    (hA : Measurable A) (hq : Measurable q) :
    Measurable (fun y => horizontalAffineRow (A y) (q y)) := by
  apply Measurable.of_eval
  intro i
  fin_cases i <;> dsimp [horizontalAffineRow] <;> fun_prop

/-- The original hidden derivative differs from the horizontal row's
velocity evaluation by just its fitted residual derivative and contact defect. -/
theorem native_horizontal_row_direction (A : Fin 4 → ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    b 5 - (horizontalAffineRow A (nativeHorizontalPoint b t) 0 +
      b 3 * horizontalAffineRow A (nativeHorizontalPoint b t) 1) =
      affineResidualSlope A b + A 3 * (b 4 + b 0) := by
  dsimp [affineResidualSlope, horizontalAffineRow, nativeHorizontalPoint]
  ring

theorem native_horizontal_row_compatibility
    (A : Fin 4 → ℝ) (b : Fin 6 → ℝ) (t E M ε : ℝ)
    (hslope : |affineResidualSlope A b| ≤ E)
    (hvertical : |A 3| ≤ M) (hdef : |b 4 + b 0| ≤ ε) :
    |horizontalAffineRow A (nativeHorizontalPoint b t) 0 +
      b 3 * horizontalAffineRow A (nativeHorizontalPoint b t) 1 - b 5| ≤ E + M * ε := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hvertical
  rw [abs_sub_comm, native_horizontal_row_direction]
  apply (abs_add_le _ _).trans
  apply add_le_add hslope
  rw [abs_mul]
  exact mul_le_mul hvertical hdef (abs_nonneg _) hM

theorem horizontalAffineRow_bound (A : Fin 4 → ℝ) (q : Fin 3 → ℝ) (K M : ℝ)
    (hK : 0 ≤ K) (_hM : 0 ≤ M) (hq₀ : |q 0| ≤ K) (hq₁ : |q 1| ≤ K)
    (hA : ∀ i : Fin 3, |A i.succ| ≤ M) :
    ∀ i, |horizontalAffineRow A q i| ≤ (1 + K) * M := by
  have hA1 : |A 1| ≤ M := hA 0
  have hA2 : |A 2| ≤ M := hA 1
  have hA3 : |A 3| ≤ M := hA 2
  have hmul (i : Fin 3) (hi : |q i| ≤ K) : |q i * A 3| ≤ K * M := by
    rw [abs_mul]
    exact mul_le_mul hi hA3 (abs_nonneg _) hK
  intro i
  fin_cases i
  · change |A 1 - q 1 * A 3| ≤ (1 + K) * M
    exact (abs_sub _ _).trans ((add_le_add hA1 (hmul 1 hq₁)).trans_eq (by ring))
  · change |A 2 + q 0 * A 3| ≤ (1 + K) * M
    exact (abs_add_le _ _).trans ((add_le_add hA2 (hmul 0 hq₀)).trans_eq (by ring))

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
