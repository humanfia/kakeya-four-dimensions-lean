-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_balanced_small_slab_reduction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_balanced_small_slab_reduction.Glue
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_balanced_small_slab_reduction`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_balanced_small_slab_reduction`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_balanced_small_slab_reduction/`
belong to this obligation.
-/

theorem WangZahlLot.wz_balanced_small_slab_reduction : (fun (T : ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space) => (fun (P : ℝ → ℝ → ℝ → ℝ → ℕ → ENNReal → Prop) => (∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1/100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (W : Set LeanEval.Analysis.WangZahlKakeya.Space), Convex ℝ W → W ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 → (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ W) → (∀ i j, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) → ENNReal.ofReal ((n : ℝ) * δ ^ 4) ≤ ENNReal.ofReal C * (MeasureTheory.volume W) ^ 2) → (∀ ζ : ℝ, 0 < ζ → ∃ η : ℝ, 0 < η ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ (1/100 : ℝ) ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ (n : ℕ) (U : ENNReal), P (δ ^ η) δ m l n U → ∃ k N : ℕ, 0 < k ∧ 0 < N ∧ ∃ ρ t M : ℝ, δ ^ (1 + ζ) ≤ ρ ∧ ρ ≤ (1/100 : ℝ) ∧ 0 < t ∧ 1 ≤ M ∧ ∃ V : Fin k → ENNReal, (∀ j, P (δ ^ ζ) ρ M (δ ^ (-ζ)) N (V j)) ∧ ENNReal.ofReal (δ ^ ζ * t) * Finset.sum Finset.univ V ≤ U ∧ M ≤ δ ^ (-ζ) * m * ((k : ℝ) * t * (N : ℝ) * ρ ^ 2) / ((n : ℝ) * δ ^ 2) ∧ δ ^ ζ ≤ l * (k : ℝ) * t ^ (1/2 : ℝ) ∧ δ ^ 2 * ((n : ℝ) / ((k : ℝ) * (N : ℝ))) ^ (1/2 : ℝ) ≤ δ ^ (-ζ) * t * ρ ^ 2)) (fun d δ m l n U => ∃ (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), (fun d δ (n : ℕ) x v Y => 0 < n ∧ (∀ i, ‖v i‖ = 1) ∧ (∀ i, T δ (x i) (v i) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) ∧ (∀ i j, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) ∧ (∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ T δ (x i) (v i)) ∧ ENNReal.ofReal (d * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i => MeasureTheory.volume (Y i))) d δ n x v Y ∧ (fun δ m (n : ℕ) x v => ∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal ((Set.ncard {i | T δ (x i) (v i) ⊆ W} : ℝ) * δ ^ 2) ≤ ENNReal.ofReal m * MeasureTheory.volume W) δ m n x v ∧ (fun δ l (n : ℕ) x v => ∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (Set.ncard {i | T δ (x i) (v i) ⊆ (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p | |inner ℝ u p - t| ≤ r})} : ℝ) ≤ ENNReal.ofReal (l * (n : ℝ)) * MeasureTheory.volume (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p | |inner ℝ u p - t| ≤ r})) δ l n x v ∧ U = MeasureTheory.volume (⋃ i, Y i))) (fun δ x v => Metric.thickening δ (segment ℝ x (x + v))) := by
  change WangZahlLot.Obl.wz_balanced_small_slab_reduction.Packing →
    WangZahlLot.Obl.wz_balanced_small_slab_reduction.Reduction
  exact WangZahlLot.Obl.wz_balanced_small_slab_reduction.reduction_of_children
    WangZahlLot.wz_balanced_affine_tube_packets
    WangZahlLot.wz_affine_packet_counting_transfer
    WangZahlLot.wz_unit_segment_convex_slab_cover
