/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/AffineContactFit.lean.
   Original source attributions below are preserved. -/
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/AffineContactFit.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_critical_intercept_concentration.Inherited.ContactGrid
import Submission.Obl.k4_scalar_angular_pair_agreement.ThreeLines

/-! Two surviving separated velocities control the horizontal gradient of an
affine difference. Its oscillation on the whole true box is then O(H squared). -/

namespace Submission.Obl.k4_critical_intercept_concentration.Inherited

noncomputable section

def affineBaseEval (A : Fin 4 → ℝ) (q : Fin 3 → ℝ) : ℝ :=
  A 0 + A 1 * q 0 + A 2 * q 1 + A 3 * q 2

theorem horizontalTrueBox_coordinate_gaps (c : Fin 5 → ℝ) (m h K : ℝ)
    (hh : 0 ≤ h) (hK : 1 ≤ K) (hv : |c 1| ≤ K)
    (hcenter : |c 3 + c 0 + m * c 1| ≤ K * h) (htilt : |c 4 - m| ≤ K * h)
    (q r : Fin 3 → ℝ) (hq : q ∈ horizontalTrueBox c m h K)
    (hr : r ∈ horizontalTrueBox c m h K) :
    |q 0 - r 0| ≤ h ∧ |q 1 - r 1| ≤ 3 * K * h ∧
      |(q 2 - r 2) + (c 0 + m * c 1) * (q 0 - r 0) - m * (q 1 - r 1)| ≤
        6 * K ^ 2 * h ^ 2 := by
  have hK0 : 0 ≤ K := by linarith
  have ht : |q 0 - r 0| ≤ h := by
    calc
      _ = |(q 0 - m) - (r 0 - m)| := by congr 1; ring
      _ ≤ |q 0 - m| + |r 0 - m| := abs_sub _ _
      _ ≤ h := by linarith [hq.1, hr.1]
  have hZ : |q 1 - r 1| ≤ 3 * K * h := by
    calc
      _ = |(q 1 - c 0 - q 0 * c 1) - (r 1 - c 0 - r 0 * c 1) +
          c 1 * (q 0 - r 0)| := by congr 1; ring
      _ ≤ |q 1 - c 0 - q 0 * c 1| + |r 1 - c 0 - r 0 * c 1| +
          |c 1 * (q 0 - r 0)| := (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ K * h + K * h + K * h := by
        apply add_le_add (add_le_add hq.2.1 hr.2.1)
        rw [abs_mul]
        exact mul_le_mul hv ht (abs_nonneg _) hK0
      _ = _ := by ring
  have herror : |(q 2 - c 2 - q 0 * c 3 - c 4 * q 1) -
      (r 2 - c 2 - r 0 * c 3 - c 4 * r 1)| ≤ 2 * K * h ^ 2 :=
    (abs_sub _ _).trans (by linarith [hq.2.2, hr.2.2])
  refine ⟨ht, hZ, ?_⟩
  calc
    _ = |(c 3 + c 0 + m * c 1) * (q 0 - r 0) + (c 4 - m) * (q 1 - r 1) +
        ((q 2 - c 2 - q 0 * c 3 - c 4 * q 1) -
          (r 2 - c 2 - r 0 * c 3 - c 4 * r 1))| := by congr 1; ring
    _ ≤ |(c 3 + c 0 + m * c 1) * (q 0 - r 0)| + |(c 4 - m) * (q 1 - r 1)| +
        |(q 2 - c 2 - q 0 * c 3 - c 4 * q 1) - (r 2 - c 2 - r 0 * c 3 - c 4 * r 1)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (K * h) * h + (K * h) * (3 * K * h) + 2 * K * h ^ 2 := by
      apply add_le_add _ herror
      apply add_le_add <;> rw [abs_mul]
      · exact mul_le_mul hcenter ht (abs_nonneg _) (mul_nonneg hK0 hh)
      · exact mul_le_mul htilt hZ (abs_nonneg _) (mul_nonneg hK0 hh)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (by nlinarith : K ≤ K ^ 2) (sq_nonneg h)]

theorem affineBaseEval_contact_difference (A : Fin 4 → ℝ) (z m : ℝ) (q r : Fin 3 → ℝ) :
    affineBaseEval A q - affineBaseEval A r =
      (A 1 - z * A 3) * (q 0 - r 0) + (A 2 + m * A 3) * (q 1 - r 1) +
        A 3 * ((q 2 - r 2) + z * (q 0 - r 0) - m * (q 1 - r 1)) := by
  unfold affineBaseEval
  ring

theorem affineBaseEval_trueBox_oscillation
    (c : Fin 5 → ℝ) (A : Fin 4 → ℝ) (m h K M : ℝ)
    (hh : 0 ≤ h) (hK : 1 ≤ K) (hM : 0 ≤ M) (hv : |c 1| ≤ K)
    (hcenter : |c 3 + c 0 + m * c 1| ≤ K * h) (htilt : |c 4 - m| ≤ K * h)
    (hY : |A 3| ≤ K) (hX : |A 1 - (c 0 + m * c 1) * A 3| ≤ M * h)
    (hZ : |A 2 + m * A 3| ≤ M * h)
    (q r : Fin 3 → ℝ) (hq : q ∈ horizontalTrueBox c m h K)
    (hr : r ∈ horizontalTrueBox c m h K) :
    |affineBaseEval A q - affineBaseEval A r| ≤ (M + 3 * K * M + 6 * K ^ 3) * h ^ 2 := by
  have hK0 : 0 ≤ K := by linarith
  have hg := horizontalTrueBox_coordinate_gaps c m h K hh hK hv hcenter htilt q r hq hr
  rw [affineBaseEval_contact_difference A (c 0 + m * c 1) m q r]
  calc
    _ ≤ |(A 1 - (c 0 + m * c 1) * A 3) * (q 0 - r 0)| +
        |(A 2 + m * A 3) * (q 1 - r 1)| +
        |A 3 * ((q 2 - r 2) + (c 0 + m * c 1) * (q 0 - r 0) - m * (q 1 - r 1))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (M * h) * h + (M * h) * (3 * K * h) + K * (6 * K ^ 2 * h ^ 2) := by
      apply add_le_add
      · apply add_le_add <;> rw [abs_mul]
        · exact mul_le_mul hX hg.1 (abs_nonneg _) (mul_nonneg hM hh)
        · exact mul_le_mul hZ hg.2.1 (abs_nonneg _) (mul_nonneg hM hh)
      · rw [abs_mul]
        exact mul_le_mul hY hg.2.2 (abs_nonneg _) hK0
    _ = _ := by ring

/-- Two actual native velocities, rather than an abstract palette witness,
control both centered horizontal derivatives of the affine difference. -/
theorem affineBaseEval_horizontal_gradient_from_two_velocities
    (A : Fin 4 → ℝ) (b : Fin 2 → Fin 6 → ℝ) (m z h K : ℝ)
    (hh : 0 ≤ h) (hK : 1 ≤ K) (hY : |A 3| ≤ K)
    (hv : ∀ i, |b i 3| ≤ K) (hsep : 1 ≤ K * |b 0 3 - b 1 3|)
    (hdefect : ∀ i, |b i 4 + b i 0| ≤ K * h)
    (hposition : ∀ i, |b i 0 + m * b i 3 - z| ≤ K * h)
    (hslope : ∀ i, |A 1 + A 2 * b i 3 + A 3 * b i 4| ≤ K * h) :
    |A 1 - z * A 3| ≤ 9 * K ^ 4 * h ∧ |A 2 + m * A 3| ≤ 9 * K ^ 4 * h := by
  have hK0 : 0 ≤ K := by linarith
  have hsample (i : Fin 2) : |(A 1 - z * A 3) + (A 2 + m * A 3) * b i 3| ≤ 3 * K ^ 2 * h := by
    have hcorrection : |b i 4 + z - m * b i 3| ≤ 2 * K * h := by
      calc
        _ = |(b i 4 + b i 0) - (b i 0 + m * b i 3 - z)| := by congr 1; ring
        _ ≤ |b i 4 + b i 0| + |b i 0 + m * b i 3 - z| := abs_sub _ _
        _ ≤ _ := by linarith [hdefect i, hposition i]
    calc
      _ = |(A 1 + A 2 * b i 3 + A 3 * b i 4) - A 3 * (b i 4 + z - m * b i 3)| := by congr 1; ring
      _ ≤ |A 1 + A 2 * b i 3 + A 3 * b i 4| + |A 3 * (b i 4 + z - m * b i 3)| := abs_sub _ _
      _ ≤ K * h + K * (2 * K * h) := by
        apply add_le_add (hslope i)
        rw [abs_mul]
        exact mul_le_mul hY hcorrection (abs_nonneg _) hK0
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (by nlinarith : K ≤ K ^ 2) hh]
  have hout := Submission.Obl.k4_scalar_angular_pair_agreement.affine_coefficients_le_of_separated
    hK (hv 0) hsep (hsample 0) (hsample 1)
  have hconst : 3 * (3 * K ^ 2 * h) * K ^ 2 = 9 * K ^ 4 * h := by ring
  rwa [hconst] at hout

/-- The two-velocity bound controls the whole affine difference on the full
true box, including points deleted from the current experiment. -/
theorem affineBaseEval_trueBox_oscillation_from_two_velocities
    (c : Fin 5 → ℝ) (A : Fin 4 → ℝ) (b : Fin 2 → Fin 6 → ℝ) (m h K : ℝ)
    (hh : 0 ≤ h) (hK : 1 ≤ K) (hc : |c 1| ≤ K)
    (hcenter : |c 3 + c 0 + m * c 1| ≤ K * h) (htilt : |c 4 - m| ≤ K * h)
    (hY : |A 3| ≤ K) (hv : ∀ i, |b i 3| ≤ K)
    (hsep : 1 ≤ K * |b 0 3 - b 1 3|)
    (hdefect : ∀ i, |b i 4 + b i 0| ≤ K * h)
    (hposition : ∀ i, |b i 0 + m * b i 3 - (c 0 + m * c 1)| ≤ K * h)
    (hslope : ∀ i, |A 1 + A 2 * b i 3 + A 3 * b i 4| ≤ K * h)
    (q r : Fin 3 → ℝ) (hq : q ∈ horizontalTrueBox c m h K)
    (hr : r ∈ horizontalTrueBox c m h K) :
    |affineBaseEval A q - affineBaseEval A r| ≤ 64 * K ^ 5 * h ^ 2 := by
  have hgrad := affineBaseEval_horizontal_gradient_from_two_velocities A b m (c 0 + m * c 1) h K
    hh hK hY hv hsep hdefect hposition hslope
  have hg := affineBaseEval_trueBox_oscillation c A m h K (9 * K ^ 4) hh hK
    (by positivity) hc hcenter htilt hY hgrad.1 hgrad.2 q r hq hr
  refine hg.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg h))
  have h₃ : K ^ 3 ≤ K ^ 5 := pow_le_pow_right₀ hK (by norm_num)
  have h₄ : K ^ 4 ≤ K ^ 5 := pow_le_pow_right₀ hK (by norm_num)
  have h₅ : 0 ≤ K ^ 5 := by positivity
  nlinarith only [h₃, h₄, h₅]

end

end Submission.Obl.k4_critical_intercept_concentration.Inherited
