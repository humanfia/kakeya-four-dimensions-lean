-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_affine_robust_cluster_estimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Proof
import Submission.WZ.ChallengeDeps
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_affine_robust_cluster_estimate`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_affine_robust_cluster_estimate`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_affine_robust_cluster_estimate/`
belong to this obligation.
-/

theorem WangZahlLot.wz_affine_robust_cluster_estimate : (fun (μ:MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) (B:Set (EuclideanSpace ℝ (Fin 3))) (T:ℝ → (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))) (D:(EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ) => (∃ K:ℝ, 1 ≤ K ∧ ∀ α b:ℝ, 0 < α → 0 < b → b ≤ 1 → ∃ c:ℝ, 0 < c ∧ ∀ δ lam m:ℝ, 0 < δ → δ ≤ (1 / 100:ℝ) → 0 < lam → lam ≤ 1 → 1 ≤ m → ∀ (n:ℕ) (x v:Fin n → (EuclideanSpace ℝ (Fin 3))) (Y:Fin n → Set (EuclideanSpace ℝ (Fin 3))), 0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ B) → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ T δ (x i) (v i)) → ENNReal.ofReal (lam * (n:ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i:Fin n => μ (Y i)) → (∀ W:Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ W → ENNReal.ofReal ((Set.ncard {i:Fin n | T δ (x i) (v i) ⊆ W}:ℝ) * δ ^ 2) ≤ ENNReal.ofReal m * μ W) → (∀ (p w:(EuclideanSpace ℝ (Fin 3))), ‖w‖ = 1 → ((Set.ncard {i:Fin n | p ∈ Y i ∧ D (v i) w ≤ b}:ℝ)) ≤ (1 / 2:ℝ) * ((Set.ncard {i:Fin n | p ∈ Y i}:ℝ))) → ENNReal.ofReal (c * δ ^ ((3 / 2:ℝ) + α) * lam ^ K * m ^ (-K) * (n:ℝ) ^ (1 / 2:ℝ)) ≤ μ (⋃ i:Fin n, Y i)) → (∃ K:ℝ, 1 ≤ K ∧ ∀ C β α:ℝ, 1 ≤ C → 0 < β → β ≤ 1 → 0 < α → ∃ c:ℝ, 0 < c ∧ ∃ s:ℝ, 0 < s ∧ s ≤ (1 / 100:ℝ) ∧ ∀ δ θ lam m:ℝ, 0 < δ → δ ≤ (1 / 100:ℝ) → δ ≤ θ → θ ≤ 1 → δ ≤ s * θ → 0 < lam → lam ≤ 1 → 1 ≤ m → ∀ (n:ℕ) (x v:Fin n → (EuclideanSpace ℝ (Fin 3))) (Y:Fin n → Set (EuclideanSpace ℝ (Fin 3))) (z w:(EuclideanSpace ℝ (Fin 3))), 0 < n → (∀ i, ‖v i‖ = 1) → ‖w‖ = 1 → (∀ i, D (v i) (w) ≤ C * θ) → (∀ i, T δ (x i) (v i) ⊆ Metric.thickening (C * θ) (segment ℝ (z) ((z) + (6:ℝ) • (w)))) → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ T δ (x i) (v i)) → (ENNReal.ofReal ((lam) * (n:ℝ) * (δ) ^ 2) ≤ Finset.sum Finset.univ (fun i:Fin n => μ (Y i))) → (∀ W:Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ W → ENNReal.ofReal ((Set.ncard {i:Fin n | T δ (x i) (v i) ⊆ W}:ℝ) * (δ) ^ 2) ≤ ENNReal.ofReal (m) * μ W) → (∀ p u r, ‖u‖ = 1 → δ ≤ r → (Set.ncard {i:Fin n | p ∈ Y i ∧ D (v i) (u) ≤ r}:ℝ) ≤ C * (r / θ) ^ β * (Set.ncard {i:Fin n | p ∈ Y i}:ℝ)) → ENNReal.ofReal (c * δ ^ ((3 / 2:ℝ) + α) * θ ^ ((1 / 2:ℝ) - α) * lam ^ K * m ^ (-K) * (n:ℝ) ^ (1 / 2:ℝ)) ≤ μ ((⋃ i:Fin n, Y i)))) MeasureTheory.volume (Metric.ball (0:(EuclideanSpace ℝ (Fin 3))) 1) (fun (δ:ℝ) (x v:(EuclideanSpace ℝ (Fin 3))) => Metric.thickening δ (segment ℝ x (x + v))) (fun (v w:(EuclideanSpace ℝ (Fin 3))) => min ‖v - w‖ ‖v + w‖) := by
  change (∃ K : ℝ, 1 ≤ K ∧ WangZahlLot.Obl.wz_affine_robust_cluster_estimate.Broad K) →
    ∃ K : ℝ, 1 ≤ K ∧ WangZahlLot.Obl.wz_affine_robust_cluster_estimate.RobustCluster K
  rintro ⟨K, hK, H⟩
  exact ⟨K, hK, WangZahlLot.Obl.wz_affine_robust_cluster_estimate.broad_to_robust hK H⟩
