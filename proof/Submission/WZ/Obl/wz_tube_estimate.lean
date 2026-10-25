-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tube_estimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_hairbrush_seed
import Submission.WZ.Obl.wz_estimate_equivalence
import Submission.WZ.Obl.wz_strict_improvement
import Submission.WZ.Obl.wz_endpoint_bootstrap
import Submission.WZ.Obl.wz_direction_convex_count
import Submission.WZ.Obl.wz_direction_density_transfer

/-!
The normalized estimates are expanded in each child's frozen type. These
abbreviations only keep the six-child glue readable; see outbox/PROOF.md
for the proof and the correspondence with Wang–Zahl Definition 1.5.
-/

namespace WangZahlLot.Obl.wz_tube_estimate

abbrev D (σ ω : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < n → (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i j : Fin n, i ≠ j → MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ∩ Metric.thickening δ (segment ℝ (x j) (x j + v j))) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)))) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) → ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i : Fin n => MeasureTheory.volume (Y i)) → (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℕ) : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (δ ^ (-η)) * MeasureTheory.volume W) → (∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p : LeanEval.Analysis.WangZahlKakeya.Space | |inner ℝ u p - t| ≤ r})} : ℕ) : ℝ)) ≤ ENNReal.ofReal ((δ ^ (-η)) * (n : ℝ)) * MeasureTheory.volume (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p : LeanEval.Analysis.WangZahlKakeya.Space | |inner ℝ u p - t| ≤ r})) → ENNReal.ofReal (a * δ ^ ((ω) + ε) * ((n : ℝ) * δ ^ 2) * ((n : ℝ) * δ) ^ (-((σ) : ℝ))) ≤ MeasureTheory.volume (⋃ i : Fin n, Y i)

abbrev E (σ ω : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < n → (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i j : Fin n, i ≠ j → MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ∩ Metric.thickening δ (segment ℝ (x j) (x j + v j))) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)))) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) → ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i : Fin n => MeasureTheory.volume (Y i)) → (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℕ) : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (m) * MeasureTheory.volume W) → (∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p : LeanEval.Analysis.WangZahlKakeya.Space | |inner ℝ u p - t| ≤ r})} : ℕ) : ℝ)) ≤ ENNReal.ofReal ((l) * (n : ℝ)) * MeasureTheory.volume (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p : LeanEval.Analysis.WangZahlKakeya.Space | |inner ℝ u p - t| ≤ r})) → ENNReal.ofReal (a * δ ^ ((ω) + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) * (m ^ (- (3 / 2 : ℝ)) * l * ((n : ℝ) * δ)) ^ (-((σ) : ℝ))) ≤ MeasureTheory.volume (⋃ i : Fin n, Y i)

end WangZahlLot.Obl.wz_tube_estimate

theorem WangZahlLot.wz_tube_estimate : ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), (∀ i : Fin n, ‖v i‖ = 1) → (∀ i j : Fin n, i ≠ j → δ ≤ ‖v i - v j‖ ∧ δ ≤ ‖v i + v j‖) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) → (∀ i : Fin n, ENNReal.ofReal (lam * δ ^ 2) ≤ MeasureTheory.volume (Y i)) → ENNReal.ofReal (c * δ ^ ε * lam ^ κ * ((n : ℝ) * δ ^ 2)) ≤ MeasureTheory.volume (⋃ i : Fin n, Y i) := by
  apply WangZahlLot.wz_direction_density_transfer WangZahlLot.wz_direction_convex_count
  exact WangZahlLot.wz_endpoint_bootstrap
    WangZahlLot.Obl.wz_tube_estimate.D WangZahlLot.Obl.wz_tube_estimate.E
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
    WangZahlLot.wz_hairbrush_seed
    WangZahlLot.wz_estimate_equivalence
    WangZahlLot.wz_strict_improvement
