import Mathlib

/-! Adapted from: here:o009
Original proofs developed for Theorem 2.17 of the supplied Kakeya paper. -/

/-!
The slope smoothing used in Theorem 2.17 of the supplied paper. A uniform
mixture of small disjoint balls around separated slopes is a probability
measure with a controlled density relative to three-dimensional volume.
-/

namespace Submission.Lib.K4ModelReduction

open MeasureTheory Metric Set
open scoped ENNReal

/-- Independently perturb a uniformly sampled slope by a ball of radius
`δ/4`. The numerical factor is the reciprocal volume of that ball. -/
noncomputable def smoothedSlopeLaw {n : ℕ}
    (s : Fin n → EuclideanSpace ℝ (Fin 3)) (δ : ℝ) :
    Measure (EuclideanSpace ℝ (Fin 3)) :=
  ENNReal.ofReal (48 / ((n : ℝ) * Real.pi * δ ^ 3)) •
    ∑ i, volume.restrict (ball (s i) (δ / 4))

private theorem smoothing_ball_volume (x : EuclideanSpace ℝ (Fin 3))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    volume (ball x (δ / 4)) = ENNReal.ofReal (Real.pi * δ ^ 3 / 48) := by
  rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- The smoothed law is normalized before any incidence selection. -/
theorem smoothedSlopeLaw_isProbabilityMeasure {n : ℕ}
    (s : Fin n → EuclideanSpace ℝ (Fin 3)) {δ : ℝ}
    (hn : 0 < n) (hδ : 0 < δ) : IsProbabilityMeasure (smoothedSlopeLaw s δ) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsum : (∑ i, volume.restrict (ball (s i) (δ / 4))) univ =
      ENNReal.ofReal ((n : ℝ) * Real.pi * δ ^ 3 / 48) := by
    simp only [Measure.finsetSum_apply, Measure.restrict_apply_univ,
      smoothing_ball_volume _ hδ.le, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    congr 1
    ring
  constructor
  rw [smoothedSlopeLaw, Measure.smul_apply, smul_eq_mul, hsum,
    ← ENNReal.ofReal_mul (by positivity)]
  have heq : 48 / ((n : ℝ) * Real.pi * δ ^ 3) *
      ((n : ℝ) * Real.pi * δ ^ 3 / 48) = 1 := by
    field_simp
  rw [heq, ENNReal.ofReal_one]

/-- Separation makes the smoothing supports disjoint, so the sum of the
restricted volume measures is one restriction of volume. -/
theorem smoothedSlopeLaw_eq_restrict {n : ℕ}
    (s : Fin n → EuclideanSpace ℝ (Fin 3)) {δ : ℝ}
    (hδ : 0 ≤ δ) (hsep : ∀ i j, i ≠ j → δ ≤ dist (s i) (s j)) :
    smoothedSlopeLaw s δ =
      ENNReal.ofReal (48 / ((n : ℝ) * Real.pi * δ ^ 3)) •
        volume.restrict (⋃ i, ball (s i) (δ / 4)) := by
  have hdisj : Pairwise (fun i j => Disjoint (ball (s i) (δ / 4)) (ball (s j) (δ / 4))) := by
    intro i j hij
    apply ball_disjoint_ball
    exact (by linarith : δ / 4 + δ / 4 ≤ δ).trans (hsep i j hij)
  rw [smoothedSlopeLaw, Measure.restrict_iUnion hdisj (fun _ => measurableSet_ball),
    Measure.sum_fintype]

/-- The full slope-density ceiling. In the Kakeya reduction one uses
`c = c₀/(k+1)^2`, so this coefficient is only a logarithmic loss. -/
theorem smoothedSlopeLaw_le_volume {n : ℕ}
    (s : Fin n → EuclideanSpace ℝ (Fin 3)) {δ c : ℝ}
    (hδ : 0 < δ) (hc : 0 < c)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (s i) (s j))
    (hmass : c ≤ (n : ℝ) * δ ^ 3) :
    smoothedSlopeLaw s δ ≤ ENNReal.ofReal (48 / (Real.pi * c)) • volume := by
  have hden : Real.pi * c ≤ (n : ℝ) * Real.pi * δ ^ 3 := by
    calc
      Real.pi * c ≤ Real.pi * ((n : ℝ) * δ ^ 3) :=
        mul_le_mul_of_nonneg_left hmass Real.pi_pos.le
      _ = _ := by ring
  have hcoef : ENNReal.ofReal (48 / ((n : ℝ) * Real.pi * δ ^ 3)) ≤
      ENNReal.ofReal (48 / (Real.pi * c)) := by
    exact ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_left (by norm_num) (mul_pos Real.pi_pos hc) hden)
  rw [smoothedSlopeLaw_eq_restrict s hδ.le hsep]
  apply Measure.le_iff.2
  intro A hA
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul' hcoef (Measure.restrict_le_self A)

end Submission.Lib.K4ModelReduction
