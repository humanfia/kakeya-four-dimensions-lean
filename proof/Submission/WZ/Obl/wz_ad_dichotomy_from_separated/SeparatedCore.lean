-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_ad_dichotomy_from_separated.SeparatedCore.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_ad_dichotomy_from_separated.ScaleLines
import Submission.WZ.Obl.wz_ad_dichotomy_from_separated.ScaleProjection
import Submission.WZ.Obl.wz_ad_dichotomy_from_separated.SetCounting

namespace WangZahlLot.Obl.wz_ad_dichotomy_from_separated

open Set Metric

def ClosedFiniteFrostman (δ C : ℝ) (S : Finset Plane) : Prop :=
  ∀ (x : Plane) (r : ℝ), δ ≤ r →
    (((↑S : Set Plane) ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * (S.card : ℝ)

def StandardTripleGeometry (S T U : Finset Plane) : Prop :=
  ∃ a c : Plane, ‖a‖ = 2 ∧ ‖c‖ = 2 ∧
    (∀ x ∈ S, dist x a ≤ 1 / 100) ∧
    (∀ x ∈ T, dist x 0 ≤ 1 / 100) ∧
    (∀ x ∈ U, dist x c ≤ 1 / 100)

/-- The separated-set kernel used in the final reduction. It is only a
definition; the geometric projection theorem remains a separate hypothesis.
The nonempty graph and its relative density are both explicit. -/
def SeparatedDichotomyAt (δ θ ε : ℝ) : Prop :=
  ∀ S T U : Finset Plane,
    (∀ x ∈ S, ‖x‖ ≤ 4) → (∀ x ∈ T, ‖x‖ ≤ 4) → (∀ x ∈ U, ‖x‖ ≤ 4) →
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) →
    (∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ dist x y) →
    (∀ x ∈ U, ∀ y ∈ U, x ≠ y → δ ≤ dist x y) →
    ClosedFiniteFrostman δ (δ ^ (-θ)) S →
    ClosedFiniteFrostman δ (δ ^ (-θ)) T →
    ClosedFiniteFrostman δ (δ ^ (-θ)) U →
    StandardTripleGeometry S T U →
    ∀ H : Finset Triple, H.Nonempty → H ⊆ S ×ˢ (T ×ˢ U) →
      δ ^ θ * (S.card : ℝ) * (T.card : ℝ) * (U.card : ℝ) ≤ (H.card : ℝ) →
      LineConclusion δ ε (↑S : Set Plane) (↑T : Set Plane) ∨
        ProjectionGain δ θ ε (↑H : Set Triple)

theorem FiniteFrostman.to_closed {δ C D : ℝ} {S : Finset Plane}
    (h : FiniteFrostman δ C S) (hδ : 0 < δ) (hCD : 2 * C ≤ D) :
    ClosedFiniteFrostman δ D S := by
  intro x r hδr
  have hcount := h.to_ncard_closed hδ x r hδr
  rw [Set.ncard_coe_finset] at hcount
  exact hcount.trans (by gcongr; exact hδ.le.trans hδr)

end WangZahlLot.Obl.wz_ad_dichotomy_from_separated
