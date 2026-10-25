-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_endpoint_bootstrap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_endpoint_bootstrap.Abstract
import Submission.WZ.Obl.wz_endpoint_bootstrap.Estimates
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_endpoint_bootstrap`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_endpoint_bootstrap`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_endpoint_bootstrap/`
belong to this obligation.
-/

open WangZahlLot.Obl.wz_endpoint_bootstrap in
theorem WangZahlLot.wz_endpoint_bootstrap : ∀ D E : ℝ → ℝ → Prop, (∀ σ ω : ℝ, D σ ω ↔ (∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < n → (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i j : Fin n, i ≠ j → MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ∩ Metric.thickening δ (segment ℝ (x j) (x j + v j))) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)))) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) → ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i : Fin n => MeasureTheory.volume (Y i)) → (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℕ) : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (δ ^ (-η)) * MeasureTheory.volume W) → (∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p : LeanEval.Analysis.WangZahlKakeya.Space | |inner ℝ u p - t| ≤ r})} : ℕ) : ℝ)) ≤ ENNReal.ofReal ((δ ^ (-η)) * (n : ℝ)) * MeasureTheory.volume (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p : LeanEval.Analysis.WangZahlKakeya.Space | |inner ℝ u p - t| ≤ r})) → ENNReal.ofReal (a * δ ^ ((ω) + ε) * ((n : ℝ) * δ ^ 2) * ((n : ℝ) * δ) ^ (-((σ) : ℝ))) ≤ MeasureTheory.volume (⋃ i : Fin n, Y i))) → (∀ σ ω : ℝ, E σ ω ↔ (∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < n → (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i j : Fin n, i ≠ j → MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)) ∩ Metric.thickening δ (segment ℝ (x j) (x j + v j))) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i)))) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) → ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i : Fin n => MeasureTheory.volume (Y i)) → (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℕ) : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (m) * MeasureTheory.volume W) → (∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p : LeanEval.Analysis.WangZahlKakeya.Space | |inner ℝ u p - t| ≤ r})} : ℕ) : ℝ)) ≤ ENNReal.ofReal ((l) * (n : ℝ)) * MeasureTheory.volume (Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 ∩ {p : LeanEval.Analysis.WangZahlKakeya.Space | |inner ℝ u p - t| ≤ r})) → ENNReal.ofReal (a * δ ^ ((ω) + ε) * m⁻¹ * ((n : ℝ) * δ ^ 2) * (m ^ (- (3 / 2 : ℝ)) * l * ((n : ℝ) * δ)) ^ (-((σ) : ℝ))) ≤ MeasureTheory.volume (⋃ i : Fin n, Y i))) → D (1 / 2 : ℝ) 0 → (∀ σ ω : ℝ, 0 ≤ σ → σ ≤ (1 / 2 : ℝ) → 0 ≤ ω → (D σ ω ↔ E σ ω)) → (∀ σ ω : ℝ, 0 < σ → σ ≤ (1 / 2 : ℝ) → 0 < ω → ω ≤ 1 → E σ ω → ∃ g : ℝ, 0 < g ∧ g ≤ ω ∧ D σ (ω - g)) → E 0 0 := by
  intro D E hD hE hseed hequiv himprove
  have hnorm : ∀ s w, D s w ↔ Estimate s w := hD
  apply (hequiv 0 0 (by norm_num) (by norm_num) le_rfl).mp
  apply endpoint_of_shift D hseed
  · intro s w w' hww h
    exact (hnorm s w').mpr (Estimate.mono_omega hww ((hnorm s w).mp h))
  · intro s t w hts h
    exact (hnorm t _).mpr (Estimate.shift hts ((hnorm s w).mp h))
  · intro s w h
    apply (hnorm s w).mpr
    apply Estimate.closed_omega
    intro e he
    exact (hnorm s (w + e)).mp (h e he)
  · intro s w hs hs1 hw hw1 h
    exact himprove s w hs hs1 hw hw1 ((hequiv s w hs.le hs1 hw.le).mp h)
