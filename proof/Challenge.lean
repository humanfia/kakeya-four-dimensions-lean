import ChallengeDeps

/-- Theorem 1.1: a subset of `ℝ⁴` containing a unit line segment in every direction has
Hausdorff dimension `4`. -/
theorem kakeya_four_dimensions (K : Set (EuclideanSpace ℝ (Fin 4)))
    (hK : ∀ e ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      ∃ a : EuclideanSpace ℝ (Fin 4), segment ℝ a (a + e) ⊆ K) :
    dimH K = 4 := by
  sorry
