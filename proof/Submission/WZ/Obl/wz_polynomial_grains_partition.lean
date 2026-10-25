-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_polynomial_grains_partition.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_polynomial_grains_partition.Grains.Main
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_polynomial_grains_partition`

Wang–Zahl Prop. A.4 (Guth–Katz polynomial-partitioning grains). The proof is
`PolyMethod.Grains.grains_frozen` (`Grains/Main.lean`): x0325's polynomial-method library
(Borsuk–Ulam, ham sandwich, Guth–Katz partitioning, tube/sign-cell counts; ported from o005
branch x0325) and grains recursion, with the sign-cell pieces of each subcube merged by mass
(`Grains/Merge.lean`, `Grains/Step.lean`) so that the number of grains is bounded without
Warren's theorem, which gives the diameter clause `K δ^(-ε) L^(-1/3)`.
-/

theorem WangZahlLot.wz_polynomial_grains_partition : ∀ε:ℝ,0<ε→∃K:ℝ,1≤K∧∀δ:ℝ,0<δ→δ≤1→∀E:Set LeanEval.Analysis.WangZahlKakeya.Space,MeasurableSet E→ E⊆Metric.ball (0:LeanEval.Analysis.WangZahlKakeya.Space) 1→∃(L:ℕ)(Q:Fin L→ MvPolynomial (Fin 3) ℝ)(z:Fin L→ LeanEval.Analysis.WangZahlKakeya.Space)(G:Fin L→ Set LeanEval.Analysis.WangZahlKakeya.Space),(∀j,Q j≠0∧((Q j).totalDegree:ℝ)≤K∧MeasurableSet (G j)∧G j⊆E∧G j⊆Metric.thickening (100*δ) {p:LeanEval.Analysis.WangZahlKakeya.Space|MvPolynomial.eval (fun i=>p i) (Q j)=0}∧G j⊆Metric.closedBall (z j) (K*δ^(-ε)*(L:ℝ)^(-(1/3:ℝ))))∧(∀j j',j≠j'→ Disjoint (G j) (G j'))∧ENNReal.ofReal (K⁻¹*δ^ε)*MeasureTheory.volume E≤∑j,MeasureTheory.volume (G j)∧(∀j,ENNReal.ofReal (K⁻¹*δ^ε/L)*MeasureTheory.volume E≤MeasureTheory.volume (G j)∧MeasureTheory.volume (G j)≤ENNReal.ofReal (K*δ^(-ε)/L)*MeasureTheory.volume E)∧∀p u:LeanEval.Analysis.WangZahlKakeya.Space,‖u‖=1→(({j|(Metric.thickening δ (segment ℝ p (p+u))∩G j).Nonempty}.ncard:ℝ)≤K*δ^(-ε)*(L:ℝ)^(1/3:ℝ)) :=
  WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod.Grains.grains_frozen
