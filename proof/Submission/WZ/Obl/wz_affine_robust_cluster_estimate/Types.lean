-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_affine_robust_cluster_estimate.Types.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Geometry

namespace WangZahlLot.Obl.wz_affine_robust_cluster_estimate
open MeasureTheory Set Metric
open scoped ENNReal

def Broad (K : ℝ) : Prop :=
  ∀ α b : ℝ, 0 < α → 0 < b → b ≤ 1 → ∃ c : ℝ, 0 < c ∧
    ∀ δ lam m : ℝ, 0 < δ → δ ≤ 1 / 100 → 0 < lam → lam ≤ 1 → 1 ≤ m →
    ∀ (n : ℕ) (x v : Fin n → E) (Y : Fin n → Set E), 0 < n →
    (∀ i, ‖v i‖ = 1) → (∀ i, tube δ (x i) (v i) ⊆ ball (0 : E) 1) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
    ENNReal.ofReal (lam * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i) →
    (∀ W : Set E, Convex ℝ W →
      ENNReal.ofReal (({i | tube δ (x i) (v i) ⊆ W}.ncard : ℝ) * δ ^ 2) ≤
        ENNReal.ofReal m * volume W) →
    (∀ p w : E, ‖w‖ = 1 →
      ({i | p ∈ Y i ∧ pd (v i) w ≤ b}.ncard : ℝ) ≤
        (1 / 2 : ℝ) * ({i | p ∈ Y i}.ncard : ℝ)) →
    ENNReal.ofReal (c * δ ^ ((3 / 2 : ℝ) + α) * lam ^ K * m ^ (-K) *
      (n : ℝ) ^ (1 / 2 : ℝ)) ≤ volume (⋃ i, Y i)

def RobustCluster (K : ℝ) : Prop :=
  ∀ C β α : ℝ, 1 ≤ C → 0 < β → β ≤ 1 → 0 < α →
    ∃ c : ℝ, 0 < c ∧ ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 100 ∧
    ∀ δ θ lam m : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ θ → θ ≤ 1 → δ ≤ s * θ →
      0 < lam → lam ≤ 1 → 1 ≤ m →
    ∀ (n : ℕ) (x v : Fin n → E) (Y : Fin n → Set E) (z w : E), 0 < n →
    (∀ i, ‖v i‖ = 1) → ‖w‖ = 1 →
    (∀ i, pd (v i) w ≤ C * θ) →
    (∀ i, tube δ (x i) (v i) ⊆ thickening (C * θ) (segment ℝ z (z + (6 : ℝ) • w))) →
    (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ tube δ (x i) (v i)) →
    ENNReal.ofReal (lam * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y i) →
    (∀ W : Set E, Convex ℝ W →
      ENNReal.ofReal (({i | tube δ (x i) (v i) ⊆ W}.ncard : ℝ) * δ ^ 2) ≤
        ENNReal.ofReal m * volume W) →
    (∀ p u r, ‖u‖ = 1 → δ ≤ r →
      ({i | p ∈ Y i ∧ pd (v i) u ≤ r}.ncard : ℝ) ≤
        C * (r / θ) ^ β * ({i | p ∈ Y i}.ncard : ℝ)) →
    ENNReal.ofReal (c * δ ^ ((3 / 2 : ℝ) + α) * θ ^ ((1 / 2 : ℝ) - α) *
      lam ^ K * m ^ (-K) * (n : ℝ) ^ (1 / 2 : ℝ)) ≤ volume (⋃ i, Y i)

end WangZahlLot.Obl.wz_affine_robust_cluster_estimate
