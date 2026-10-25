import Submission.Obl.k4_native_calibrated_homogeneous_remainder.Models
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.PolynomialBounds

/-! Bounded chart parameters and subpower losses of the raw certificate. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable def RemainderGeometry.assignmentMass {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (k : ℕ) (b : Fin (q.W k)) : ENNReal :=
  p.ν (a.φ k) ((a.parent k).γ (a.worlds k b)) ((a.parent k).A (a.worlds k b))

noncomputable def RemainderGeometry.densityRatio {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (k : ℕ) (b : Fin (q.W k)) : ℝ :=
  |Matrix.det ((a.parent k).Q (a.worlds k b))| / (a.assignmentMass k b).toReal

/-- Every full assignment has a positive finite probability mass. -/
theorem RemainderGeometry.assignmentMass_bounds {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (hp : Valid p) (k : ℕ) (b : Fin (q.W k)) :
    0 < (a.assignmentMass k b).toReal ∧ (a.assignmentMass k b).toReal ≤ 1 := by
  obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  letI : IsProbabilityMeasure (p.ν (a.φ k) ((a.parent k).γ (a.worlds k b))) :=
    ((hfmt (a.φ k)).2.2.2.1 _).1
  have hfin : a.assignmentMass k b ≠ ∞ := measure_ne_top _ _
  have hle : a.assignmentMass k b ≤ 1 := by
    simpa [RemainderGeometry.assignmentMass] using
      (measure_mono (μ := p.ν (a.φ k) ((a.parent k).γ (a.worlds k b)))
        (subset_univ ((a.parent k).A (a.worlds k b))))
  exact ⟨ENNReal.toReal_pos (ne_of_gt (a.prior_pos k b)) hfin,
    by simpa using ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ∞) hle⟩

/-- The density normalization factors of all charts have one fixed polynomial
range, including zero-weight worlds. -/
theorem RemainderGeometry.densityRatio_bounds {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (hp : Valid p) (k : ℕ) (b : Fin (q.W k)) :
    0 < a.densityRatio k b ∧
      q.N k ^ (-((3 * a.M + 1 : ℕ) : ℝ)) ≤ a.densityRatio k b ∧
      a.densityRatio k b ≤ q.N k ^ (3 * a.M + 1) := by
  have hc := (a.parent_valid k).2.2 (a.worlds k b)
  obtain ⟨hm0, hm1⟩ := a.assignmentMass_bounds hp k b
  have hband := frame_prior_ratio_band ((a.parent k).Q (a.worlds k b))
    (hp.scale_ge_two (a.φ k)) hc.1 hc.2.2.1 hm0 hm1 (a.prior_inverse_bound k b)
  rw [← a.same_base k] at hband
  exact ⟨div_pos (abs_pos.mpr hc.1) hm0, hband⟩

/-- The raw chart slack remains subpower in the normalized family's base. -/
theorem RemainderGeometry.slack_subpower {p q : Data} {r h w : ℝ}
    (a : RemainderGeometry p q r h w) (hp : Valid p) :
    (∀ k, 1 ≤ a.κ k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, a.κ k ≤ q.N k ^ ε := by
  refine ⟨a.slack_one, fun ε hε => ?_⟩
  filter_upwards [a.error_limit.eventually (gt_mem_nhds hε)] with k hk
  rw [a.same_base k]
  exact (a.slack_bound k).trans
    (Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one (a.φ k)) hk.le)

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
