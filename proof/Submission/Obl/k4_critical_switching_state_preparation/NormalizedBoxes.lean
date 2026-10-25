/- Adapted from this LOT tree, obligation o212, session x0762, commit ecff5a0a89fd,
   Submission/Obl/k4_critical_intercept_concentration/NormalizedBoxes.lean.
   Existing source attributions below are preserved. -/
/- Adapted from this LOT tree, obligation o201, session x0697, commit 74bd9a876bac,
   Submission/Obl/k4_horizontal_critical_rate_candidates/NormalizedBoxes.lean.
   Original source attributions below are preserved. -/
import Submission.Obl.k4_critical_switching_state_preparation.Inherited.ContactNormalization

namespace Submission.Obl.k4_critical_switching_state_preparation

open Inherited

noncomputable section

/-- A descendant contact box has the same fourth-power scale in its parent's
coordinates. One actual meeting point controls its centered position. -/
theorem normalized_box_bounds
    (H t₀ z₀ y₀ v₀ m h K : ℝ) (c : Fin 5 → ℝ) (q₀ : Fin 3 → ℝ)
    (hH : 0 < H) (hh : 0 ≤ h) (hrel : h / H ≤ 1) (hK : 1 ≤ K)
    (hv₀ : |v₀| ≤ K) (hc : |c 1| ≤ K)
    (hcenter : |c 3 + c 0 + m * c 1| ≤ K * h) (htilt : |c 4 - m| ≤ K * h)
    (hq₀ : q₀ ∈ horizontalTrueBox c m h K)
    (hposition : |horizontalFrame H t₀ z₀ y₀ v₀ q₀ 1| ≤ K) :
    let c' := horizontalBoxCoefficients H t₀ z₀ y₀ v₀ c
    let m' := (m - t₀) / H
    |c' 1| ≤ 4 * K ^ 2 ∧ |c' 0 + m' * c' 1| ≤ 4 * K ^ 2 ∧
      |c' 3 + c' 0 + m' * c' 1| ≤ (4 * K ^ 2) * (h / H) ∧
      |c' 4 - m'| ≤ (4 * K ^ 2) * (h / H) ∧
      ∀ q ∈ horizontalTrueBox c m h K,
        horizontalFrame H t₀ z₀ y₀ v₀ q ∈
          horizontalTrueBox c' m' (h / H) (4 * K ^ 2) := by
  let c' := horizontalBoxCoefficients H t₀ z₀ y₀ v₀ c
  let m' := (m - t₀) / H
  let q' := horizontalFrame H t₀ z₀ y₀ v₀ q₀
  have hK0 : 0 ≤ K := by linarith
  have hKsq : K ≤ K ^ 2 := by nlinarith
  have hrel0 : 0 ≤ h / H := div_nonneg hh hH.le
  have hv : |c' 1| ≤ 2 * K := by
    change |c 1 - v₀| ≤ 2 * K
    exact (abs_sub _ _).trans (by linarith only [hc, hv₀])
  have hq' : q' ∈ horizontalTrueBox c' m' (h / H) K :=
    (horizontalFrame_mem_trueBox H t₀ z₀ y₀ v₀ m h K hH c q₀).mpr hq₀
  have hgap : |c' 0 + m' * c' 1 - q' 1| ≤ 2 * K * (h / H) := by
    calc
      _ = |-(q' 1 - c' 0 - q' 0 * c' 1) + (m' - q' 0) * c' 1| := by congr 1; ring
      _ ≤ |q' 1 - c' 0 - q' 0 * c' 1| + |(m' - q' 0) * c' 1| := by
        simpa only [abs_neg] using abs_add_le (-(q' 1 - c' 0 - q' 0 * c' 1))
          ((m' - q' 0) * c' 1)
      _ ≤ K * (h / H) + ((h / H) / 2) * (2 * K) := by
        apply add_le_add hq'.2.1
        rw [abs_mul]
        exact mul_le_mul (by simpa only [abs_sub_comm] using hq'.1) hv (abs_nonneg _)
          (by positivity)
      _ = _ := by ring
  have hpos : |c' 0 + m' * c' 1| ≤ 4 * K ^ 2 := by
    calc
      _ ≤ |c' 0 + m' * c' 1 - q' 1| + |q' 1| := by
        simpa only [sub_zero] using abs_sub_le (c' 0 + m' * c' 1) (q' 1) 0
      _ ≤ 2 * K * (h / H) + K := add_le_add hgap hposition
      _ ≤ 4 * K ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_left hrel (by positivity : 0 ≤ 2 * K), hKsq]
  have hct := horizontalBoxCoefficients_center_bound H t₀ z₀ y₀ v₀ m h K c
    hH hh hK hv₀ hcenter htilt
  refine ⟨hv.trans (by nlinarith), hpos, hct.1.trans ?_, hct.2.trans ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (by nlinarith : 2 * K ^ 2 ≤ 4 * K ^ 2) hrel0
  · exact mul_le_mul_of_nonneg_right (by nlinarith : K ≤ 4 * K ^ 2) hrel0
  · intro q hq
    have hq' := (horizontalFrame_mem_trueBox H t₀ z₀ y₀ v₀ m h K hH c q).mpr hq
    refine ⟨hq'.1, hq'.2.1.trans ?_, hq'.2.2.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right (by nlinarith : K ≤ 4 * K ^ 2) hrel0
    · exact mul_le_mul_of_nonneg_right (by nlinarith : K ≤ 4 * K ^ 2) (sq_nonneg _)

end

end Submission.Obl.k4_critical_switching_state_preparation
