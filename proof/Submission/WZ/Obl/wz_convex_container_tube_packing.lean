-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_convex_container_tube_packing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_convex_container_tube_packing.Packing
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_convex_container_tube_packing`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_convex_container_tube_packing`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_convex_container_tube_packing/`
belong to this obligation.
-/

theorem WangZahlLot.wz_convex_container_tube_packing : (fun (T : ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space) => ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1/100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (W : Set LeanEval.Analysis.WangZahlKakeya.Space), Convex ℝ W → W ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1 → (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ W) → (∀ i j, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) → ENNReal.ofReal ((n : ℝ) * δ ^ 4) ≤ ENNReal.ofReal C * (MeasureTheory.volume W) ^ 2) (fun δ x v => Metric.thickening δ (segment ℝ x (x + v))) := by
  refine ⟨1000000, by norm_num, ?_⟩
  intro δ hδ hδmax n x v W hWconv hWball hv hTW hover
  exact WangZahlLot.Obl.wz_convex_container_tube_packing.packing hδ x v
    (ne_top_of_le_ne_top MeasureTheory.measure_ball_lt_top.ne
      (MeasureTheory.measure_mono hWball)) hv hTW hover
