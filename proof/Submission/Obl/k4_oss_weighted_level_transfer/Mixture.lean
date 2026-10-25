import Submission.Obl.k4_oss_collision_cauchy_schwarz.Cells

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Submission.Obl.k4_oss_weighted_level_transfer

/-- Collision mass in a closed interval about the diagonal. -/
noncomputable def collision (r : ℝ) (μ : Measure ℝ) : ℝ≥0∞ :=
  (μ.prod μ) {p : ℝ × ℝ | |p.1 - p.2| ≤ r}

lemma ennreal_sum_sq_le {I : Type*} [Fintype I] (f : I → ℝ≥0∞)
    (hf : ∀ i, f i ≠ ∞) :
    (∑ i, f i) * (∑ i, f i) ≤ (Fintype.card I : ℝ≥0∞) * ∑ i, f i * f i := by
  let g : I → ℝ≥0 := fun i => (f i).toNNReal
  have hg (i : I) : (g i : ℝ≥0∞) = f i := ENNReal.coe_toNNReal (hf i)
  simp_rw [← hg]
  exact_mod_cast (by simpa only [pow_two, Finset.card_univ] using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := g)))

/-- A finite sum of laws costs just the number of laws in the collision estimate. -/
theorem collision_sum_le {I : Type*} [Fintype I]
    (μ : I → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)] {r : ℝ} (hr : 0 < r) :
    collision r (∑ i, μ i) ≤
      3 * (Fintype.card I : ℝ≥0∞) * ∑ i, collision r (μ i) := by
  classical
  let C := Submission.Obl.k4_oss_collision_cauchy_schwarz.cell r
  calc
    _ ≤ 3 * ∑' k : ℤ, (∑ i, μ i) (C k) * (∑ i, μ i) (C k) :=
      Submission.Obl.k4_oss_collision_cauchy_schwarz.collision_le_three_cell_energy _ hr
    _ = 3 * ∑' k : ℤ, (∑ i, μ i (C k)) * (∑ i, μ i (C k)) := by
      simp only [Measure.finsetSum_apply]
    _ ≤ 3 * ∑' k : ℤ, (Fintype.card I : ℝ≥0∞) * ∑ i, μ i (C k) * μ i (C k) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact ENNReal.tsum_le_tsum (fun k => ennreal_sum_sq_le _
        (fun i => measure_ne_top (μ i) (C k)))
    _ = 3 * (Fintype.card I : ℝ≥0∞) * ∑ i, ∑' k : ℤ, μ i (C k) * μ i (C k) := by
      rw [ENNReal.tsum_mul_left, mul_assoc]
      congr 2
      simpa only [tsum_fintype] using
        (ENNReal.tsum_comm (f := fun (k : ℤ) (i : I) => μ i (C k) * μ i (C k)))
    _ ≤ 3 * (Fintype.card I : ℝ≥0∞) * ∑ i, collision r (μ i) := by
      gcongr with i
      exact Submission.Obl.k4_oss_collision_cauchy_schwarz.cell_energy_le_collision _ hr

end Submission.Obl.k4_oss_weighted_level_transfer
