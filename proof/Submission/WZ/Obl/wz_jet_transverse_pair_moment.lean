-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_transverse_pair_moment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_jet_transverse_pair_moment.TransverseRich
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_jet_transverse_pair_moment`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_jet_transverse_pair_moment`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_jet_transverse_pair_moment/`
belong to this obligation.
-/

theorem WangZahlLot.wz_jet_transverse_pair_moment : ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ) (δ η κ : ℝ), 0 < δ → δ ≤ 1 → 0 ≤ η → 0 < κ → κ ≤ 1 → (∀ i, ‖q i‖ ≤ 10) → (∀ i, ContDiff ℝ 2 (g i)) → (∀ (i j : Fin n) (z : ℝ), z ∈ Set.Icc (-1 : ℝ) 1 → dist (q i) (q j) ≤ 30 * (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ∧ (|g i z - g j z| + |deriv (g i) z - deriv (g j) z| + |deriv (deriv (g i)) z - deriv (deriv (g j)) z|) ≤ 19 * dist (q i) (q j)) → (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) → (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 → (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ ^ (-η) * (r / δ)) → MeasureTheory.lintegral MeasureTheory.volume (fun p : ℝ × ℝ => Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => if i = j then 0 else Set.indicator ({p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g i p.2| ≤ δ} ∩ {p : ℝ × ℝ | p.2 ∈ Set.Icc (-1) 1 ∧ |p.1 - g j p.2| ≤ δ} ∩ {p : ℝ × ℝ | κ * dist (q i) (q j) ≤ |deriv (g i) p.2 - deriv (g j) p.2|}) (fun _ => (1 : ENNReal)) p))) ≤ ENNReal.ofReal (C * δ ^ (-2 * η - τ) / κ) := by
  intro τ hτ
  obtain ⟨C, hC, hbound⟩ :=
    WangZahlLot.Obl.wz_jet_transverse_pair_moment.transverse_moment_bound τ hτ
  refine ⟨C, hC, ?_⟩
  intro n q g δ η κ hδ hδ1 hη hκ hκ1 hq hg hjet hsep hcount
  exact hbound hδ hδ1 hκ hκ1 hq hg hjet hsep hcount
