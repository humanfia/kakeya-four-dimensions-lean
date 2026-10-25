-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.kakeya_three_le_dimH_of_tube_estimate.Reduction
open scoped NNReal ENNReal

/-!
# Hausdorff dimension from the tube estimate

The proof uses finite ball covers of a Hausdorff-null compact set, a positive-area
cap of directions localized by segment midpoint, and geometric pigeonholes in the
cover scale. Finite separated nets give both the shading volume and the number of
directions. Choosing the power loss after the tube exponent makes the lower bound
incompatible with arbitrarily small Hausdorff covering cost.
-/

theorem WangZahlLot.kakeya_three_le_dimH_of_tube_estimate : (∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), (∀ i : Fin n, ‖v i‖ = 1) → (∀ i j : Fin n, i ≠ j → δ ≤ ‖v i - v j‖ ∧ δ ≤ ‖v i + v j‖) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ Metric.thickening δ (segment ℝ (x i) (x i + v i))) → (∀ i : Fin n, ENNReal.ofReal (lam * δ ^ 2) ≤ MeasureTheory.volume (Y i)) → ENNReal.ofReal (c * δ ^ ε * lam ^ κ * ((n : ℝ) * δ ^ 2)) ≤ MeasureTheory.volume (⋃ i : Fin n, Y i)) → ∀ K : Set LeanEval.Analysis.WangZahlKakeya.Space, LeanEval.Analysis.WangZahlKakeya.IsKakeya K → 3 ≤ dimH K := by
  intro hTube K hK
  apply (WangZahlLot.Seed.Kakeya.three_le_dimH_iff K).mpr
  intro d hd
  by_cases hd0 : d = 0
  · subst d
    have hdim : (0 : ℝ≥0∞) < dimH K := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1)
      (WangZahlLot.Seed.Kakeya.IsKakeya.one_le_dimH hK)
    rw [hausdorffMeasure_of_lt_dimH hdim]
    exact ENNReal.top_ne_zero
  · exact WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.hausdorffMeasure_ne_zero_of_tube_estimate
      hTube hK (by exact_mod_cast (pos_iff_ne_zero.mpr hd0)) (by exact_mod_cast hd)
