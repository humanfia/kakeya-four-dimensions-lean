import Submission.Obl.k4_oss_unit_decay.Defs

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Submission.Obl.k4_oss_unit_decay

lemma small_rpow_bound (B p : ℝ) (hp : 0 < p) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ → B * δ ^ p ≤ 1 := by
  have hc : ContinuousAt (fun δ : ℝ => B * δ ^ p) 0 :=
    continuousAt_const.mul (Real.continuous_rpow_const hp.le).continuousAt
  have he : ∀ᶠ δ : ℝ in 𝓝 0, B * δ ^ p < 1 :=
    hc.tendsto.eventually (gt_mem_nhds (by simp [Real.zero_rpow hp.ne']))
  rcases Metric.eventually_nhds_iff.mp he with ⟨r, hr, h⟩
  refine ⟨min r 1, lt_min hr (by norm_num), min_le_right _ _, ?_⟩
  intro δ hδ hδ₀
  exact (h (by simpa [Real.dist_eq, abs_of_pos hδ] using
    (hδ₀.trans_le (min_le_left r 1)))).le

lemma small_absorb (B a b : ℝ) (hab : a < b) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ → B * δ ^ (-a) ≤ δ ^ (-b) := by
  obtain ⟨δ₀, hδ₀, hδ₀1, h⟩ := small_rpow_bound B (b - a) (sub_pos.mpr hab)
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ hδ hδsmall
  calc
    B * δ ^ (-a) = (B * δ ^ (b - a)) * δ ^ (-b) := by
      rw [mul_assoc, ← Real.rpow_add hδ]
      congr 2
      ring
    _ ≤ 1 * δ ^ (-b) := mul_le_mul_of_nonneg_right (h δ hδ hδsmall)
      (Real.rpow_nonneg hδ.le _)
    _ = _ := one_mul _

end Submission.Obl.k4_oss_unit_decay
