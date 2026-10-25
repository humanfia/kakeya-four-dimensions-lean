import Mathlib
import ChallengeDeps
import Submission.Obl.k4_weighted_convex_tubes.Reduction
import Submission.Obl.k4_weighted_convex_tubes.SamplingBridge
set_option linter.unusedVariables false

/-!
# `Submission.k4_weighted_convex_tubes`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_weighted_convex_tubes`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_weighted_convex_tubes/`
belong to this obligation.
-/

theorem Submission.k4_weighted_convex_tubes : (∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ a : ℝ, 0 < a ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → EuclideanSpace ℝ (Fin 3)) (Y : Fin n → Set (EuclideanSpace ℝ (Fin 3))), (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) → (∀ i : Fin n, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ MeasureTheory.volume (Y i)) → (∀ W : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ W → ∀ S : Finset (Fin n), (∀ i ∈ S, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W) → ENNReal.ofReal ((S.card : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (δ ^ (-η)) * MeasureTheory.volume W) → ENNReal.ofReal (a * δ ^ ε * (n : ℝ) * δ ^ 2) ≤ MeasureTheory.volume (⋃ i : Fin n, Y i)) → ∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c → ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ), 1 ≤ D → ∀ (n : ℕ) (x v : Fin n → EuclideanSpace ℝ (Fin 3)) (Y : Fin n → Set (EuclideanSpace ℝ (Fin 3))) (ω : Fin n → ℝ) (A : ℝ), (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, Metric.thickening (1 / (100 * (D : ℝ))) (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ Metric.thickening (1 / (100 * (D : ℝ))) (segment ℝ (x i) (x i + v i))) → (∀ i : Fin n, 0 < ω i) → 0 < A → (∀ i : Fin n, c * (D : ℝ) ^ (-η) / (D : ℝ) ^ 2 ≤ (MeasureTheory.volume (Y i)).toReal) → (∀ W : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ W → ∀ S : Finset (Fin n), (∀ i ∈ S, Metric.thickening (1 / (100 * (D : ℝ))) (segment ℝ (x i) (x i + v i)) ⊆ W) → ENNReal.ofReal ((∑ i ∈ S, ω i) / (D : ℝ) ^ 2) ≤ ENNReal.ofReal A * MeasureTheory.volume W) → (∑ i : Fin n, ω i) / (D : ℝ) ^ 2 ≤ C * A * (D : ℝ) ^ ε * (MeasureTheory.volume (⋃ i : Fin n, Y i)).toReal := by
  intro hset
  apply Submission.Obl.k4_weighted_convex_tubes.weighted_of_sampling
    Submission.Obl.k4_weighted_convex_tubes.sampling_principle
  intro ε hε
  obtain ⟨η, hη, a, ha, hbound⟩ := hset ε hε
  refine ⟨η, hη, a, ha, ?_⟩
  intro r hr hr100 n x v Y hv hb hY hYT hdense hcount
  exact hbound r hr hr100 n x v Y hv hb hY hYT hdense
    (fun W hW F hFW => hcount W hW F (Finset.subset_univ _) hFW)
