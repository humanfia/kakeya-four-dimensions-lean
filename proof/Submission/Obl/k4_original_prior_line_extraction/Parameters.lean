import Mathlib
import ChallengeDeps

namespace Submission.Obl.k4_original_prior_line_extraction

open Filter
open scoped Topology

/-- Fixed constants and the two density losses are absorbed by any prescribed exponent. -/
lemma extraction_parameters (D A C b c η : ℝ) (hD : 0 ≤ D)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hb : 0 < b) (hc : 0 < c) (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧
      ∀ R ε : ℝ, R₀ ≤ R → 0 < ε → ε ≤ ε₀ →
        D * R ^ (-1 + ε) ≤ (c / 2) * R ^ (-ε) ∧
        A * R ^ ε ≤ R ^ η ∧ C * R ^ (2 * ε) ≤ R ^ η ∧
        R ^ (-η) ≤ b * R ^ (-ε) ∧ ε ≤ η := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hηhalf : 0 < η / 2 := by positivity
  obtain ⟨r₁, hr₁⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hhalf).eventually (eventually_ge_atTop (2 * D / c)))
  obtain ⟨r₂, hr₂⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hηhalf).eventually
      (eventually_ge_atTop (max A (max C b⁻¹))))
  refine ⟨min (η / 4) (1 / 4), lt_min (by positivity) (by norm_num),
    max 2 (max r₁ r₂), le_max_left _ _, ?_⟩
  intro R ε hR hε hε₀
  have hRtwo : 2 ≤ R := (le_max_left _ _).trans hR
  have hRone : 1 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  have hsmall := hr₁ R ((le_max_left r₁ r₂).trans ((le_max_right _ _).trans hR))
  have hlarge := hr₂ R ((le_max_right r₁ r₂).trans ((le_max_right _ _).trans hR))
  have hεη : ε ≤ η / 4 := hε₀.trans (min_le_left _ _)
  have hεquarter : ε ≤ 1 / 4 := hε₀.trans (min_le_right _ _)
  have hlargeA : A ≤ R ^ (η / 2) := (le_max_left _ _).trans hlarge
  have hlargeC : C ≤ R ^ (η / 2) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hlargeb : b⁻¹ ≤ R ^ (η / 2) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hzero : D * R ^ (-1 + 2 * ε) ≤ c / 2 := by
    have hDlarge : D ≤ (c / 2) * R ^ (1 / 2 : ℝ) := by
      have := (div_le_iff₀ hc).mp hsmall
      nlinarith
    calc
      D * R ^ (-1 + 2 * ε) ≤ D * R ^ (-(1 / 2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hD
        apply Real.rpow_le_rpow_of_exponent_le hRone
        linarith
      _ ≤ ((c / 2) * R ^ (1 / 2 : ℝ)) * R ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hDlarge (Real.rpow_nonneg hRpos.le _)
      _ = c / 2 := by rw [mul_assoc, ← Real.rpow_add hRpos]; norm_num
  refine ⟨?_, ?_, ?_, ?_, by linarith⟩
  · calc
      D * R ^ (-1 + ε) = (D * R ^ (-1 + 2 * ε)) * R ^ (-ε) := by
        rw [mul_assoc, ← Real.rpow_add hRpos]
        congr 2
        ring
      _ ≤ (c / 2) * R ^ (-ε) :=
        mul_le_mul_of_nonneg_right hzero (Real.rpow_nonneg hRpos.le _)
  · calc
      A * R ^ ε ≤ R ^ (η / 2) * R ^ ε :=
        mul_le_mul_of_nonneg_right hlargeA (Real.rpow_nonneg hRpos.le _)
      _ = R ^ (η / 2 + ε) := (Real.rpow_add hRpos _ _).symm
      _ ≤ R ^ η := Real.rpow_le_rpow_of_exponent_le hRone (by linarith)
  · calc
      C * R ^ (2 * ε) ≤ R ^ (η / 2) * R ^ (2 * ε) :=
        mul_le_mul_of_nonneg_right hlargeC (Real.rpow_nonneg hRpos.le _)
      _ = R ^ (η / 2 + 2 * ε) := (Real.rpow_add hRpos _ _).symm
      _ ≤ R ^ η := Real.rpow_le_rpow_of_exponent_le hRone (by linarith)
  · have hinv : R ^ (-(η / 2)) ≤ b := by
      have := inv_anti₀ (inv_pos.mpr hb) hlargeb
      simpa [Real.rpow_neg hRpos.le] using this
    calc
      R ^ (-η) = R ^ (-(η / 2)) * R ^ (-(η / 2)) := by
        rw [← Real.rpow_add hRpos]
        congr 1
        ring
      _ ≤ b * R ^ (-ε) := by
        apply mul_le_mul hinv
          (Real.rpow_le_rpow_of_exponent_le hRone (by linarith))
          (Real.rpow_nonneg hRpos.le _) hb.le

end Submission.Obl.k4_original_prior_line_extraction
