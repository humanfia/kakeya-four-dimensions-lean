-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extreme_offset_fibre_estimate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_extreme_offset_fibre_estimate.Estimate
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_extreme_offset_fibre_estimate`

At extreme offsets, each transverse tube has projection fibres of length at
most `δ ^ 2`. Volume-preserving shears and a measurable hull give an outer-area
bound from the total shading mass. Exponent monotonicity finishes the estimate.
-/

theorem WangZahlLot.wz_extreme_offset_fibre_estimate : (fun T : ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space => (fun (H : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) → Prop) (F : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → Prop) (N : (ℝ → ℝ) → Prop) (P : (ℝ → ℝ) → Set LeanEval.Analysis.WangZahlKakeya.Space → Set (ℝ × ℝ)) => ∀ ε η δ : ℝ, 0 < δ → δ ≤ 1 → η ≤ ε → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), H η δ n x v Y → (∀ i, (1/2 : ℝ) ≤ |v i 2|) → ∀ f : ℝ → ℝ, N f → 2 + 6 / δ ≤ |f 0| → ENNReal.ofReal (δ ^ ε) ≤ MeasureTheory.volume (P f (⋃ i, Y i))) (fun η δ n x v Y => 0 < n ∧ (∀ i, ‖v i‖ = 1) ∧ (∀ i, T δ (x i) (v i) ⊆ Metric.ball 0 1) ∧ (∀ i j, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) ∧ (∀ i, MeasurableSet (Y i)) ∧ (∀ i, Y i ⊆ T δ (x i) (v i)) ∧ ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i => MeasureTheory.volume (Y i))) (fun η δ n x v => ∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (Set.ncard {i | T δ (x i) (v i) ⊆ W} : ℝ) ≤ ENNReal.ofReal (δ ^ (-η) * (n : ℝ)) * MeasureTheory.volume W) (fun f : ℝ → ℝ => ContDiff ℝ 2 f ∧ ∀ z : ℝ, z ∈ Set.Icc (-1) 1 → 1 ≤ |deriv f z| ∧ |deriv f z| ≤ 2 ∧ |deriv (deriv f) z| ≤ (1/100 : ℝ)) (fun (f : ℝ → ℝ) (E : Set LeanEval.Analysis.WangZahlKakeya.Space) => (fun p : LeanEval.Analysis.WangZahlKakeya.Space => (p 0 + f (p 2) * p 1, p 2)) '' E)) (fun (δ : ℝ) (x v : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening δ (segment ℝ x (x + v))) := by
  intro ε η δ hδ hδ1 hη n x v Y hH ht f hf hoff
  rcases hH with ⟨hn, hv, hball, hoverlap, hmeas, hY, hmass⟩
  have hp := WangZahlLot.Obl.wz_extreme_offset_fibre_estimate.family_projection_estimate
    hδ hn x v Y hv ht hball hY hmass hf.1 (fun z hz => (hf.2 z hz).2.1) hoff
  exact (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hη)).trans hp
