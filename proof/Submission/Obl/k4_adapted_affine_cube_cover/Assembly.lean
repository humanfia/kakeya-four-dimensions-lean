import Mathlib

namespace Submission.Obl.k4_adapted_affine_cube_cover

open MeasureTheory Set
open scoped ENNReal

/-- Disjoint measurable tests in a set give the required domination of measures. -/
theorem sum_restrict_le_of_disjoint {E ι : Type*} [MeasurableSpace E] [Fintype ι]
    (μ : Measure E) (Q : ι → Set E) (B : Set E)
    (hQ : ∀ i, MeasurableSet (Q i)) (hdisj : Pairwise (fun i j => Disjoint (Q i) (Q j)))
    (hsub : ∀ i, Q i ⊆ B) :
    (∑ i, μ.restrict (Q i)) ≤ μ.restrict B := by
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hdisj hQ]
  exact Measure.restrict_mono (iUnion_subset hsub) le_rfl

/-- The total real mass of disjoint compact tests is at most the volume of the ball. -/
theorem sum_volume_le_ball {n : ℕ} {ι : Type*} [Fintype ι]
    (Q : ι → Set (EuclideanSpace ℝ (Fin n))) (c : EuclideanSpace ℝ (Fin n))
    (hQ : ∀ i, IsCompact (Q i)) (hdisj : Pairwise (fun i j => Disjoint (Q i) (Q j)))
    (hsub : ∀ i, Q i ⊆ Metric.ball c 1) :
    (∑ i, (volume (Q i)).toReal) ≤ (volume (Metric.ball c 1)).toReal := by
  calc
    (∑ i, (volume (Q i)).toReal) = volume.real (⋃ i, Q i) := by
      symm
      exact measureReal_iUnion_fintype hdisj (fun i => (hQ i).measurableSet)
        (fun i => (hQ i).measure_ne_top)
    _ ≤ (volume (Metric.ball c 1)).toReal :=
      measureReal_mono (iUnion_subset hsub) (measure_ball_lt_top.ne)

/-- Turn a uniform per-test volume lower bound into the reciprocal body-volume count. -/
theorem card_bound_of_volume {n k : ℕ}
    (Q : Fin k → Set (EuclideanSpace ℝ (Fin n))) (c : EuclideanSpace ℝ (Fin n))
    (hQ : ∀ i, IsCompact (Q i)) (hdisj : Pairwise (fun i j => Disjoint (Q i) (Q j)))
    (hsub : ∀ i, Q i ⊆ Metric.ball c 1)
    {p u : ℝ} (hp : 0 < p) (hu : 0 < u)
    (hlower : ∀ i, p * u ≤ (volume (Q i)).toReal) :
    (k : ℝ) ≤ ((volume (Metric.ball c 1)).toReal / p) * u⁻¹ := by
  have hsum : (k : ℝ) * (p * u) ≤ (volume (Metric.ball c 1)).toReal := by
    calc
      (k : ℝ) * (p * u) = ∑ _i : Fin k, p * u := by simp
      _ ≤ ∑ i : Fin k, (volume (Q i)).toReal := Finset.sum_le_sum (fun i _ => hlower i)
      _ ≤ _ := sum_volume_le_ball Q c hQ hdisj hsub
  apply (le_div_iff₀ hu).2
  apply (le_div_iff₀ hp).2
  nlinarith [hsum]

/-- A finite cover by enlarged tiles converts into a lower bound for the smaller tiles' mass. -/
theorem mass_bound_of_cover {n k : ℕ}
    (Q : Fin k → Set (EuclideanSpace ℝ (Fin n))) (c : EuclideanSpace ℝ (Fin n))
    (hQ : ∀ i, IsCompact (Q i))
    (hcover : volume (Metric.ball c (1 / 4)) ≤ (2 : ℝ≥0∞) ^ n * ∑ i, volume (Q i)) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 4))).toReal / (2 : ℝ) ^ n ≤
      ∑ i, (volume (Q i)).toReal := by
  have hfin (i : Fin k) : volume (Q i) ≠ ⊤ := (hQ i).measure_ne_top
  have hfinSum : (∑ i : Fin k, volume (Q i)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => hfin i)
  have hfinProd : (2 : ℝ≥0∞) ^ n * (∑ i : Fin k, volume (Q i)) ≠ ⊤ := by
    finiteness
  have h := ENNReal.toReal_mono hfinProd hcover
  rw [Measure.addHaar_ball_center volume c, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_sum (fun i _ => hfin i)] at h
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr (by simpa only [mul_comm] using h)

end Submission.Obl.k4_adapted_affine_cube_cover
