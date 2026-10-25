import Submission.Obl.k4_raw_critical_segment_forests.Saturation

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- Saturation fixes the Jacobian-to-prior exponent to the original depth
profile, for every retained parent simultaneously. -/
theorem PreparedParent.jacobian_ratio {p : Data} (hp : Valid p) {k M D : ℕ}
    {r ε κ : ℝ} {a : Atlas p k} (ha : PreparedParent p M D r ε κ a) (b : Fin a.C) :
    p.N k ^ (p.f r - ε) ≤ |Matrix.det (a.Q b)| / (p.ν k (a.γ b) (a.A b)).toReal ∧
      |Matrix.det (a.Q b)| / (p.ν k (a.γ b) (a.A b)).toReal ≤ p.N k ^ (p.f r + ε) := by
  have hN := hp.scale_pos k
  have hκ : 0 < κ := lt_of_lt_of_le zero_lt_one ha.1
  have hs := ha.prior_saturation hp b
  have hf : 0 < p.N k ^ (p.f r) := Real.rpow_pos_of_pos hN _
  have hcancel : p.N k ^ (p.f r) * p.N k ^ (-p.f r) = 1 := by
    rw [← Real.rpow_add hN, add_neg_cancel, Real.rpow_zero]
  have hlow : p.N k ^ (p.f r) / κ ≤
      |Matrix.det (a.Q b)| / (p.ν k (a.γ b) (a.A b)).toReal := by
    apply (div_le_div_iff₀ hκ hs.1).mpr
    have h := mul_le_mul_of_nonneg_left hs.2.2 hf.le
    have heq : p.N k ^ (p.f r) * (κ * p.N k ^ (-p.f r) * |Matrix.det (a.Q b)|) =
        κ * |Matrix.det (a.Q b)| := by
      calc
        _ = κ * |Matrix.det (a.Q b)| * (p.N k ^ (p.f r) * p.N k ^ (-p.f r)) := by ring
        _ = _ := by rw [hcancel, mul_one]
    rw [heq] at h
    nlinarith only [h]
  have hhigh : |Matrix.det (a.Q b)| / (p.ν k (a.γ b) (a.A b)).toReal ≤
      κ * p.N k ^ (p.f r) := by
    apply (div_le_iff₀ hs.1).mpr
    have h := mul_le_mul_of_nonneg_left ((div_le_iff₀ hκ).mp hs.2.1) hf.le
    rw [← mul_assoc, hcancel, one_mul] at h
    nlinarith only [h]
  constructor
  · rw [Real.rpow_sub hN]
    exact (div_le_div_of_nonneg_left hf.le hκ ha.2.2.1).trans hlow
  · apply hhigh.trans
    rw [Real.rpow_add hN, mul_comm (p.N k ^ (p.f r))]
    exact mul_le_mul_of_nonneg_right ha.2.2.1 hf.le

end
end Submission.Obl.k4_raw_critical_segment_forests
