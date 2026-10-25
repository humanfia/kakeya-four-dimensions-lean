import Submission.Obl.k4_plank_estimate.SetEstimate

namespace Submission.Obl.k4_plank_estimate

/-- The proved unweighted estimate in the all-subfinsets form used by sampling. -/
theorem unweighted_set_estimate_finset : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ a : ℝ, 0 < a ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → EuclideanSpace ℝ (Fin 3)) (Y : Fin n → Set (EuclideanSpace ℝ (Fin 3))), (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) → (∀ i : Fin n, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ MeasureTheory.volume (Y i)) → (∀ W : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ W → ∀ S : Finset (Fin n), (∀ i ∈ S, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W) → ENNReal.ofReal ((S.card : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (δ ^ (-η)) * MeasureTheory.volume W) → ENNReal.ofReal (a * δ ^ ε * (n : ℝ) * δ ^ 2) ≤ MeasureTheory.volume (⋃ i : Fin n, Y i) := by
  classical
  intro ε hε
  obtain ⟨η, hη, a, ha, h⟩ := unweighted_set_estimate ε hε
  refine ⟨η, hη, a, ha, ?_⟩
  intro δ hδ hδ100 n x v Y hv hball hmeas hsub hdens hcluster
  have hcluster' (W : Set (EuclideanSpace ℝ (Fin 3))) (hW : Convex ℝ W) :
      ENNReal.ofReal ((Set.ncard {i : Fin n |
        Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℝ) * δ ^ 2) ≤
          ENNReal.ofReal (δ ^ (-η)) * MeasureTheory.volume W := by
    let S : Finset (Fin n) := {i : Fin n |
      Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W}.toFinset
    have hh := hcluster W hW S (by
      intro i hi
      simpa only [S, Set.mem_toFinset, Set.mem_setOf_eq] using hi)
    simpa only [S, Set.ncard_eq_toFinset_card'] using hh
  simpa only [mul_assoc] using
    h δ hδ hδ100 n x v Y hv hball hmeas hsub hdens hcluster'

end Submission.Obl.k4_plank_estimate
