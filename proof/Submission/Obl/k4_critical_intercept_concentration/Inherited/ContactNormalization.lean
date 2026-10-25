/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/ContactNormalization.lean.
   Original source attributions below are preserved. -/
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/ContactNormalization.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_critical_intercept_concentration.Inherited.ContactGrid
import Submission.Obl.k4_critical_intercept_concentration.Inherited.HorizontalNormalization

/-! True horizontal boxes transform with transverse scale H squared. -/

namespace Submission.Obl.k4_critical_intercept_concentration.Inherited

noncomputable section

def horizontalBoxCoefficients (H t₀ z₀ y₀ v₀ : ℝ) (c : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![(c 0 + t₀ * c 1 - z₀) / H,
    c 1 - v₀,
    (c 2 + t₀ * c 3 + c 4 * z₀ - y₀) / H ^ 2,
    (c 3 + (c 4 - t₀) * v₀ + z₀) / H,
    (c 4 - t₀) / H]

theorem horizontalFrame_box_time (H t₀ z₀ y₀ v₀ m : ℝ) (q : Fin 3 → ℝ) :
    horizontalFrame H t₀ z₀ y₀ v₀ q 0 - (m - t₀) / H = (q 0 - m) / H := by
  simp only [horizontalFrame, Matrix.cons_val_zero]
  ring

theorem horizontalFrame_box_Z (H t₀ z₀ y₀ v₀ : ℝ) (hH : H ≠ 0)
    (c : Fin 5 → ℝ) (q : Fin 3 → ℝ) :
    let c' := horizontalBoxCoefficients H t₀ z₀ y₀ v₀ c
    let q' := horizontalFrame H t₀ z₀ y₀ v₀ q
    q' 1 - c' 0 - q' 0 * c' 1 = (q 1 - c 0 - q 0 * c 1) / H := by
  dsimp [horizontalBoxCoefficients, horizontalFrame]
  field_simp
  ring

theorem horizontalFrame_box_Y (H t₀ z₀ y₀ v₀ : ℝ) (hH : H ≠ 0)
    (c : Fin 5 → ℝ) (q : Fin 3 → ℝ) :
    let c' := horizontalBoxCoefficients H t₀ z₀ y₀ v₀ c
    let q' := horizontalFrame H t₀ z₀ y₀ v₀ q
    q' 2 - c' 2 - q' 0 * c' 3 - c' 4 * q' 1 =
      (q 2 - c 2 - q 0 * c 3 - c 4 * q 1) / H ^ 2 := by
  dsimp [horizontalBoxCoefficients, horizontalFrame]
  field_simp
  ring

/-- Membership in the complete true box is preserved by the contact frame,
with block length h/H and the same error constant. -/
theorem horizontalFrame_mem_trueBox (H t₀ z₀ y₀ v₀ m h K : ℝ) (hH : 0 < H)
    (c : Fin 5 → ℝ) (q : Fin 3 → ℝ) :
    horizontalFrame H t₀ z₀ y₀ v₀ q ∈
      horizontalTrueBox (horizontalBoxCoefficients H t₀ z₀ y₀ v₀ c)
        ((m - t₀) / H) (h / H) K ↔ q ∈ horizontalTrueBox c m h K := by
  change (_ ≤ (h / H) / 2 ∧ _ ≤ K * (h / H) ∧ _ ≤ K * (h / H) ^ 2) ↔ _
  rw [horizontalFrame_box_time, horizontalFrame_box_Z _ _ _ _ _ hH.ne',
    horizontalFrame_box_Y _ _ _ _ _ hH.ne', abs_div, abs_div, abs_div,
    abs_of_pos hH, abs_of_pos (sq_pos_of_pos hH)]
  rw [show (h / H) / 2 = (h / 2) / H by ring,
    show K * (h / H) = (K * h) / H by ring,
    show K * (h / H) ^ 2 = (K * h ^ 2) / H ^ 2 by ring]
  simp only [div_le_div_iff_of_pos_right hH,
    div_le_div_iff_of_pos_right (sq_pos_of_pos hH)]
  rfl

theorem horizontalBoxCoefficients_tilt (H t₀ z₀ y₀ v₀ m : ℝ) (c : Fin 5 → ℝ) :
    horizontalBoxCoefficients H t₀ z₀ y₀ v₀ c 4 - (m - t₀) / H = (c 4 - m) / H := by
  dsimp [horizontalBoxCoefficients]
  ring

theorem horizontalBoxCoefficients_center (H t₀ z₀ y₀ v₀ m : ℝ) (c : Fin 5 → ℝ) :
    let c' := horizontalBoxCoefficients H t₀ z₀ y₀ v₀ c
    c' 3 + c' 0 + ((m - t₀) / H) * c' 1 =
      (c 3 + c 0 + m * c 1 + (c 4 - m) * v₀) / H := by
  dsimp [horizontalBoxCoefficients]
  ring

/-- Centered slope and tilt remain bounded after normalization. In particular
the fourth-power contact count applies at every descendant-to-parent scale. -/
theorem horizontalBoxCoefficients_center_bound
    (H t₀ z₀ y₀ v₀ m h K : ℝ) (c : Fin 5 → ℝ)
    (hH : 0 < H) (hh : 0 ≤ h) (hK : 1 ≤ K) (hv₀ : |v₀| ≤ K)
    (hcenter : |c 3 + c 0 + m * c 1| ≤ K * h)
    (htilt : |c 4 - m| ≤ K * h) :
    let c' := horizontalBoxCoefficients H t₀ z₀ y₀ v₀ c
    |c' 3 + c' 0 + ((m - t₀) / H) * c' 1| ≤ 2 * K ^ 2 * (h / H) ∧
    |c' 4 - (m - t₀) / H| ≤ K * (h / H) := by
  have hK0 : 0 ≤ K := by linarith
  constructor
  · rw [horizontalBoxCoefficients_center, abs_div, abs_of_pos hH]
    apply (div_le_iff₀ hH).mpr
    have hnum : |c 3 + c 0 + m * c 1 + (c 4 - m) * v₀| ≤ K * h + K * h * K := by
      apply (abs_add_le _ _).trans
      apply add_le_add hcenter
      rw [abs_mul]
      exact mul_le_mul htilt hv₀ (abs_nonneg _) (mul_nonneg hK0 hh)
    have hKsq : K ≤ K ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hKsq hh
    have heq : 2 * K ^ 2 * (h / H) * H = 2 * K ^ 2 * h := by field_simp
    rw [heq]
    nlinarith only [hnum, hmul]
  · rw [horizontalBoxCoefficients_tilt, abs_div, abs_of_pos hH]
    convert div_le_div_of_nonneg_right htilt hH.le using 1 <;> ring

end

end Submission.Obl.k4_critical_intercept_concentration.Inherited
