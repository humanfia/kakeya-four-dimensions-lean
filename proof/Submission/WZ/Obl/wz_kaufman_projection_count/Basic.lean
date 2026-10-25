-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_kaufman_projection_count.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/- Definitions used by the Kaufman proof, extracted from this tree's o103
branch x0272, commit f2e1c96 (Basic.lean and SeparatedCore.lean). -/
namespace WangZahlLot.Obl.wz_kaufman_projection_count

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A finite cover by closed balls. -/
def Covers {X : Type*} [PseudoMetricSpace X] (r : ℝ) (S : Set X)
    {m : ℕ} (c : Fin m → X) : Prop :=
  S ⊆ ⋃ j, Metric.closedBall (c j) r

/-- The counting Frostman condition at scales at least `δ`. -/
def ClosedFiniteFrostman (δ C : ℝ) (S : Finset Plane) : Prop :=
  ∀ (x : Plane) (r : ℝ), δ ≤ r →
    (((↑S : Set Plane) ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * (S.card : ℝ)

end WangZahlLot.Obl.wz_kaufman_projection_count
