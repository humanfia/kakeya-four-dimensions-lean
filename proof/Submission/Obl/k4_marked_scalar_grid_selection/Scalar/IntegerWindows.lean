/- Adapted from this LOT tree, obligation o100, session x0340, commit fb1668b,
   Submission/Obl/k4_scalar_marked_profile_selection/IntegerWindows.lean. -/
import Submission.Lib.K4QuadraticSublevel

noncomputable section

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open Set MeasureTheory Metric
open scoped ENNReal

/-- Integer entries whose physical locations lie in a fixed real window. -/
def integerWindow (a c R : ℝ) : Set ℤ := {z | |a * (z : ℝ) - c| ≤ R}

theorem integerWindow_finite_card {a c R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    (integerWindow a c R).Finite ∧
      ((integerWindow a c R).ncard : ℝ) ≤ 8 * R / a + 2 := by
  have hdiam : ∀ x ∈ closedBall c R, ∀ y ∈ closedBall c R, dist x y ≤ 2 * R := by
    intro x hx y hy
    have h := dist_triangle x c y
    rw [dist_comm c y] at h
    linarith [mem_closedBall.mp hx, mem_closedBall.mp hy]
  obtain ⟨hfin, hcard⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    (closedBall c R) (show 0 ≤ 2 * R by positivity) ha 0 hdiam
  have hsub : integerWindow a c R ⊆
      (fun x : ℝ => ⌊(x - 0) / a⌋) '' closedBall c R := by
    intro z hz
    refine ⟨a * (z : ℝ), ?_, ?_⟩
    · simpa only [mem_closedBall, Real.dist_eq, integerWindow, mem_ofPred_eq] using hz
    · simp [ha.ne']
  have hfin' := hfin.subset hsub
  refine ⟨hfin', ?_⟩
  have hn := Set.ncard_le_ncard hsub hfin
  calc
    _ ≤ (((fun x : ℝ => ⌊(x - 0) / a⌋) '' closedBall c R).ncard : ℝ) := by exact_mod_cast hn
    _ ≤ 2 * (2 * R) / a + 2 := hcard
    _ ≤ 8 * R / a + 2 := by
      simp only [div_eq_mul_inv]
      nlinarith [mul_nonneg hR (inv_nonneg.mpr ha.le)]

theorem integerWindow_count_le {a c R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    Measure.count (integerWindow a c R) ≤ ENNReal.ofReal (8 * R / a + 2) := by
  obtain ⟨hfin, hcard⟩ := integerWindow_finite_card (c := c) ha hR
  rw [Measure.count_apply_finite _ hfin]
  rw [Set.ncard_eq_toFinset_card _ hfin] at hcard
  exact_mod_cast (show ((hfin.toFinset.card : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (8 * R / a + 2) by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcard)

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
