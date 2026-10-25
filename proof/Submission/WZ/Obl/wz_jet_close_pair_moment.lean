-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_close_pair_moment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_jet_close_pair_moment.ClosePairs
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_jet_close_pair_moment`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_jet_close_pair_moment`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_jet_close_pair_moment/`
belong to this obligation.
-/

theorem WangZahlLot.wz_jet_close_pair_moment : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ) (δ η R : ℝ), 0 < δ → δ ≤ 1 → 0 ≤ η → δ ≤ R → (∀ i, ‖q i‖ ≤ 10) → (∀ i, ContDiff ℝ 2 (g i)) → (∀ (i j : Fin n) (z : ℝ), z ∈ Set.Icc (-1 : ℝ) 1 → dist (q i) (q j) ≤ 30 * (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ∧ (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ≤ 19 * dist (q i) (q j)) → (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) → (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 → (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ ^ (-η) * (r / δ)) → MeasureTheory.lintegral MeasureTheory.volume (fun p : ℝ × ℝ => Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => if dist (q i) (q j) < R then Set.indicator ({p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} ∩ {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g j p.2| ≤ δ}) (fun _ => (1 : ENNReal)) p else 0))) ≤ ENNReal.ofReal (C * δ ^ (-2 * η) * Real.sqrt (R / δ)) := by
  obtain ⟨C, hC, hbound⟩ := WangZahlLot.Obl.wz_jet_close_pair_moment.close_pair_moment_bound
  exact ⟨C, hC, fun n q g δ η R hδ hδ1 hη hδR hq hg hjet hsep hcount =>
    hbound hδ hδ1 hη hδR hq hg hjet hsep hcount⟩
