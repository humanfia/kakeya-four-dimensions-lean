/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/FrostmanExtension.lean -/
import Mathlib

/-! Extend finite-range ball caps using the unchanged total-mass ceiling. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

open Set MeasureTheory
open scoped ENNReal

theorem original_ball_cap_extension {X Y : Type*} [MeasurableSpace X] [PseudoMetricSpace Y]
    (ν : Measure X) (a : X → Y) (p : ℝ≥0∞) (ξ σ d A C Q : ℝ)
    (hξ : 0 < ξ) (hσ : 0 < σ) (hd : 0 ≤ d) (hA : 0 ≤ A)
    (htotal : ν Set.univ ≤ p * ENNReal.ofReal A)
    (hfine : ∀ b r, ξ ≤ r → r ≤ σ → ν {l | a l ∈ Metric.ball b r} ≤
      p * ENNReal.ofReal (C * r ^ d))
    (hCQ : C ≤ Q) (hAQ : A * σ ^ (-d) ≤ Q) :
    ∀ b r, ξ ≤ r → ν {l | a l ∈ Metric.ball b r} ≤ p * ENNReal.ofReal (Q * r ^ d) := by
  intro b r hr
  have hrpos : 0 < r := hξ.trans_le hr
  by_cases hrs : r ≤ σ
  · exact (hfine b r hr hrs).trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCQ (Real.rpow_nonneg hrpos.le _))))
  · have hpow : σ ^ d ≤ r ^ d := Real.rpow_le_rpow hσ.le (le_of_not_ge hrs) hd
    have hnum : A ≤ Q * r ^ d := by
      calc
        _ = (A * σ ^ (-d)) * σ ^ d := by rw [mul_assoc,← Real.rpow_add hσ]; simp
        _ ≤ (A * σ ^ (-d)) * r ^ d := mul_le_mul_of_nonneg_left hpow
          (mul_nonneg hA (Real.rpow_nonneg hσ.le _))
        _ ≤ _ := mul_le_mul_of_nonneg_right hAQ (Real.rpow_nonneg hrpos.le _)
    exact (measure_mono (Set.subset_univ _)).trans
      (htotal.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hnum)))

end Submission.Obl.k4_scalar_grid_parameter_preparation
