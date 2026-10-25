-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.Certificates.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

/-- The source tree retains a quarter-radius buffer before edgewise copying. -/
def SourceTower (T:ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space) :=
  (fun (δ a u:ℝ) (B m:ℕ) (x v:Fin m → LeanEval.Analysis.WangZahlKakeya.Space) =>
  ∃ J:ℕ, 0 < J ∧ J + 2 ≤ B ∧
  ∃ (r:ℕ → ℝ) (k:ℕ → ℕ)
    (z w:(j:ℕ) → Fin (k j) → LeanEval.Analysis.WangZahlKakeya.Space)
    (p:(j:ℕ) → Fin (k (j+1)) → Fin (k j)) (M:ℕ → ℝ),
    r 0 = (1/100:ℝ) ∧ r J = δ ∧ k 0 = 1 ∧
    (∃ e:Fin m ≃ Fin (k J), ∀ i:Fin m, z J (e i) = x i ∧ w J (e i) = v i) ∧
    δ ^ (a/2) ≤ (1/100:ℝ) ∧ (m:ℝ) ≤ δ ^ (-7:ℝ) ∧
    (∀ j:ℕ, j ≤ J → δ ≤ r j ∧ r j ≤ (1/100:ℝ) ∧ 0 < k j ∧
      (∀ i:Fin (k j), ‖w j i‖ = 1 ∧ T (r j) (z j i) (w j i) ⊆ Metric.ball 0 (3/4:ℝ)) ∧
      (∀ W:Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W →
        ENNReal.ofReal ((Set.ncard {i:Fin (k j) | T (r j) (z j i) (w j i) ⊆ W}:ℝ) * (r j)^2) ≤
        ENNReal.ofReal (δ ^ (-u)) * MeasureTheory.volume W)) ∧
    (∀ j:ℕ, j < J → 16 * r (j+1) ≤ r j ∧ δ ^ (a/2) * r j ≤ r (j+1) ∧ 1 ≤ M j ∧
      (∀ i:Fin (k j), M j / 2 ≤ (Set.ncard {s:Fin (k (j+1)) | p j s = i}:ℝ) ∧
        (Set.ncard {s:Fin (k (j+1)) | p j s = i}:ℝ) ≤ M j) ∧
      (∀ i:Fin (k (j+1)), T (r (j+1)) (z (j+1) i) (w (j+1) i) ⊆
        T (r j / 4) (z j (p j i)) (w j (p j i)))))

/-- An adjacent counted chain, with the budgets needed for global assembly. -/
def CountedChain (T:ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space) :=
  (fun (δ a b:ℝ) (B m:ℕ) (x v:Fin m → LeanEval.Analysis.WangZahlKakeya.Space) =>
  ∃ J:ℕ, 0 < J ∧ J + 1 ≤ B ∧
  ∃ (r:ℕ → ℝ) (k:ℕ → ℕ)
    (z w:(j:ℕ) → Fin (k j) → LeanEval.Analysis.WangZahlKakeya.Space)
    (p:(j:ℕ) → Fin (k (j+1)) → Fin (k j)) (L κ:ℝ),
    r 0 = 1 ∧ r J = δ ∧ k 0 = 1 ∧
    (∃ e:Fin m ≃ Fin (k J), ∀ i:Fin m, z J (e i) = x i ∧ w J (e i) = v i) ∧
    (∀ i:Fin m, ‖v i‖ = 1 ∧ T δ (x i) (v i) ⊆ Metric.ball 0 1) ∧
    (∀ j:ℕ, j ≤ J → 0 < k j ∧ ∀ i:Fin (k j), ‖w j i‖ = 1) ∧
    (∀ j:ℕ, j < J → 0 < r (j+1) ∧ r (j+1) < r j ∧ δ ^ (a/2) * r j ≤ r (j+1) ∧
      ∀ i:Fin (k (j+1)), T (r (j+1)) (z (j+1) i) (w (j+1) i) ⊆
        T (r j) (z j (p j i)) (w j (p j i))) ∧
    (∀ j:ℕ, j < J → ∀ i:Fin (k j), κ * (r j)^2 ≤
      (Set.ncard {s:Fin (k (j+1)) | p j s = i}:ℝ) * (r (j+1))^2) ∧
    (∀ j:ℕ, j < J → ∀ (i:Fin (k j)) (W:Set LeanEval.Analysis.WangZahlKakeya.Space), Convex ℝ W →
      ENNReal.ofReal ((Set.ncard {s:Fin (k (j+1)) | p j s = i ∧
        T (r (j+1)) (z (j+1) s) (w (j+1) s) ⊆ W}:ℝ) * (r (j+1))^2) ≤
      ENNReal.ofReal L * MeasureTheory.volume W) ∧
    1 ≤ L ∧ 0 < κ ∧ κ ≤ 1 ∧ (131072 * L)^J ≤ δ ^ (-b) ∧ δ ^ b ≤ κ^J)

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
