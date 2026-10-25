import Submission.Obl.k4_critical_affine_derivative_preparation.ContinuousNormalization
import Mathlib.Probability.ConditionalProbability

namespace Submission.Obl.k4_contact_affine_residual_candidate_transfer

open Set MeasureTheory ProbabilityTheory
open Submission.Obl.k4_critical_affine_derivative_preparation

/-- Restricting to a parent and normalizing its time and full prior costs
exactly the original density ceiling. The incidence success mass is not
used as the denominator. -/
theorem original_parent_normalized_domination {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (μ : Measure (α × ℝ))
    (A : Set α) (G : Set (α × ℝ)) {t₀ q K : ℝ}
    (hq : 0 < q) (hK : 0 ≤ K) (hA : ν A ≠ 0)
    (hG : G ⊆ A ×ˢ (univ : Set ℝ))
    (hdom : μ ≤ ENNReal.ofReal K • ν.prod volume) :
    (ENNReal.ofReal q * ν A)⁻¹ •
      (μ.restrict G).map (fun p : α × ℝ => (p.1, (p.2 - t₀) / q)) ≤
        ENNReal.ofReal K • ((cond ν A).prod volume) := by
  have hraw : μ.restrict G ≤ ENNReal.ofReal K • (ν.restrict A).prod volume := by
    have hh := Measure.restrict_mono hG hdom
    rwa [Measure.restrict_smul, ← Measure.restrict_prod_eq_prod_univ] at hh
  have hν : (ν.restrict A) univ ≠ 0 := by simpa only [Measure.restrict_apply_univ] using hA
  have hνreal : 0 < ν.real A := ENNReal.toReal_pos hA (measure_ne_top ν A)
  let W := q * ν.real A
  have hW : 0 < W := mul_pos hq hνreal
  have hscale : ENNReal.ofReal W = ENNReal.ofReal q * ν A := by
    change ENNReal.ofReal (q * ν.real A) = _
    rw [ENNReal.ofReal_mul hq.le, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top ν A)]
  have hh := original_continuous_normalized_domination (ν.restrict A) (μ.restrict G)
    t₀ q K W hq hK hW hν hraw
  have hfactor : K * q * (ν.restrict A).real univ / W = K := by
    simp only [measureReal_def, Measure.restrict_apply_univ, W]
    field_simp [hq.ne', show (ν A).toReal ≠ 0 from hνreal.ne']
  rw [hfactor, ENNReal.ofReal_inv_of_pos hW, hscale] at hh
  simp only [Measure.restrict_apply_univ] at hh
  exact hh

end Submission.Obl.k4_contact_affine_residual_candidate_transfer
